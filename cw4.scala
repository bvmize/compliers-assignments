// A Small Compiler for the WHILE Language (jasmin)

// =================================================
// LEXER
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp
case class STAR(r: Rexp) extends Rexp
case class RANGE(cs: Set[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp
case class RECD(x: String, r: Rexp) extends Rexp

abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
case class Range_(v: Val) extends Val
case class Optional(v: Val) extends Val

def charlist2rexp(s: List[Char]): Rexp = s match {
  case Nil => ONE
  case c :: Nil => CHAR(c)
  case c :: s => SEQ(CHAR(c), charlist2rexp(s))
}

implicit def string2rexp(s: String): Rexp = charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def |(s: Rexp) = ALT(r, s)

  def % = STAR(r)

  def ~(s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def |(r: Rexp) = ALT(s, r)

  def |(r: String) = ALT(s, r)

  def % = STAR(s)

  def ~(r: Rexp) = SEQ(s, r)

  def ~(r: String) = SEQ(s, r)

  def $(r: Rexp) = RECD(s, r)
}

def nullable(r: Rexp): Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RANGE(chars) => false
  case PLUS(r) => nullable(r)
  case OPTIONAL(_) => true
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
}

def der(c: Char, r: Rexp): Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) =>
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RECD(_, r1) => der(c, r1)
  case RANGE(chars) =>
    if (chars(c)) ONE
    else ZERO
  case PLUS(r) => SEQ(der(c, r), STAR(r))
  case OPTIONAL(r) => der(c, r)
  case NTIMES(r, i) =>
    if (i == 0) ZERO
    else SEQ(der(c, r), NTIMES(r, i - 1))
}

def ders(s: List[Char], r: Rexp): Rexp = s match {
  case Nil => r
  case c :: s => ders(s, der(c, r))
}

def flatten(v: Val): String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
  // NEW
  case Range_(v) => flatten(v)
  case Optional(v) => flatten(v)
  // Don't need values for Ntimes/Plus (use Stars)
}

def env(v: Val): List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v)) :: env(v)
  // NEW
  case Range_(v) => env(v)
  case Optional(v) => env(v)
  // Don't need values for Ntimes/Plus (use Stars)
}

def mkeps(r: Rexp): Val = r match {
  case ONE => Empty
  case ALT(r1, r2) =>
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
  // NEW

  //case RANGE(cs) => No such case. Like 0 and CHAR, it can never match the empty string

  // PLUS can match the empty string if r is nullable...
  // If I just use Stars(Nil), when matching "", returns Stars(List()) rather than Stars(List(Empty))... possibly cosmetic but I prefer it?
  case PLUS(r) => Stars(List[Val](mkeps(r)))
  // optional always matches the empty string (doesn't matter what's inside, like Stars)
  case OPTIONAL(r) => Optional(Empty)
  // ntimes can match the empty string if n = 0 or r is nullable
  // Similar thing to Plus...
  // not sure if this is totally necessary but I like the way it looks
  case NTIMES(r, n) => Stars(List.fill(n)(mkeps(r)))
}

def inj(r: Rexp, c: Char, v: Val): Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1) :: vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c)
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))

  // NEW
  // how to make a range of Chr() for each Char in cs??
  case (RANGE(cs), Empty) => Chr(c)

  // format of nullable PLUS(r) ders will always be nullable • STAR(r)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1) :: vs)

  // mkeps will always be whatever was inside the ?...
  // Ever reached by der?
  case (OPTIONAL(r), _) => Optional(inj(r, c, v))

  // format of value will always be (the match) • Stars
  case (NTIMES(r, n), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1) :: vs)
}

def lex(r: Rexp, s: List[Char]): Val = s match {
  case Nil => if (nullable(r)) mkeps(r)
  else throw new Exception("Not matched")
  case c :: cs => inj(r, c, lex(der(c, r), cs))
}

def lexing(r: Rexp, s: String): Val = lex(r, s.toList)

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v: Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v: Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v: Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v: Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) =
  (v: Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) =
  (v: Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v: Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
      else (ALT(r1s, r2s), F_ALT(f1s, f2s))
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s, r2s), F_SEQ(f1s, f2s))
    }
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
}

def lex_simp(r: Rexp, s: List[Char]): Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else throw new Exception("Not matched")
  case c :: cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String): Val = lex_simp(r, s.toList)

val SYM = RANGE(('a' to 'z').toSet ++ ('A' to 'Z').toSet)
val DIGIT = RANGE(('0' to '9').toSet)
val NONZERO = RANGE(('1' to '9').toSet)

val KEYWORD: Rexp = "while" | "do" | "if" | "then" | "else" | "true" | "false" | "read" | "write" | "skip" | "for" | "upto"
val OP: Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | ":=" | "&&" | "||" | "<="
val STRING: Rexp = """"""" ~ SYM.% ~ """""""
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val LCURLYBRACE: Rexp = "{"
val RCURLYBRACE: Rexp = "}"
val SEMI: Rexp = ";"
val WHITESPACE = PLUS(" " | "\n" | "\t")
val ID = SYM ~ ("_" | SYM | DIGIT).%
val NUM = "0" | NONZERO ~ DIGIT.%

val WHILE_REGS = (("k" $ KEYWORD) |
  ("i" $ ID) |
  ("o" $ OP) |
  ("n" $ NUM) |
  ("s" $ SEMI) |
  ("str" $ STRING) |
  ("p" $ (LPAREN | RPAREN)) |
  ("b" $ (LCURLYBRACE | RCURLYBRACE)) |
  ("w" $ WHITESPACE)
  ).%

//==============================================================
// PARSER

abstract class Parser[I <% Seq[_], T] {
  def parse(ts: I): Set[(T, I)]

  def parse_all(ts: I): Set[T] =
    for ((head, tail) <- parse(ts); if (tail.isEmpty)) yield head
}

class SeqParser[I <% Seq[_], T, S](p: => Parser[I, T], q: => Parser[I, S]) extends Parser[I, (T, S)] {
  def parse(sb: I) =
    for ((head1, tail1) <- p.parse(sb);
          (head2, tail2) <- q.parse(tail1)) yield ((head1, head2), tail2)
}

class AltParser[I <% Seq[_], T](p: => Parser[I, T], q: => Parser[I, T]) extends Parser[I, T] {
  def parse(sb: I) = p.parse(sb) ++ q.parse(sb)
}

class FunParser[I <% Seq[_], T, S](p: => Parser[I, T], f: T => S) extends Parser[I, S] {
  def parse(sb: I) =
    for ((head, tail) <- p.parse(sb)) yield (f(head), tail)
}

case object StringParser extends Parser[List[(String, String)], String] {
  def parse(tokens: List[(String, String)]) = {
    if (tokens(0)._1 == "str") {
      Set((tokens(0)._2, tokens.tail))
    } else {
      Set()
    }
  }
}

case object NumParser extends Parser[List[(String, String)], Int] {
  def parse(tokens: List[(String, String)]) = {
    if (tokens(0)._1 == "n"){
      Set((tokens(0)._2.toInt, tokens.tail))
    } else {
      Set()
    }
  }
}

case object IdParser extends Parser[List[(String, String)], String] {
  def parse(tokens: List[(String, String)]) = {
    if (tokens(0)._1 == "i") {
      Set((tokens(0)._2, tokens.tail))
    } else {
      Set()
    }
  }
}

case class TokenParser(token: (String, String)) extends Parser[List[(String, String)], (String, String)] {
  def parse(tokens: List[(String, String)]) = {
    if (!tokens.isEmpty && tokens(0) == token)
      Set((token, tokens.tail)) else
      Set()
  }
}

implicit def token2parser(token: (String, String)) = TokenParser(token)


implicit def TokenOps(s: (String, String)) = new {
  def ||(q: => Parser[List[(String, String)], (String, String)]) = new AltParser[List[(String, String)], (String, String)](s, q)

  def ||(r: (String, String)) = new AltParser[List[(String, String)], (String, String)](s, r)

  def ==>[S](f: => ((String, String)) => S) = new FunParser[List[(String, String)], (String, String), S](s, f)

  def ~[S](q: => Parser[List[(String, String)], S]) =
    new SeqParser[List[(String, String)], (String, String), S](s, q)

  def ~(r: (String, String)) =
    new SeqParser[List[(String, String)], (String, String), (String, String)](s, r)
}

implicit def ParserOps[I <% Seq[_], T](p: Parser[I, T]) = new {
  def ||(q: => Parser[I, T]) = new AltParser[I, T](p, q)

  def ==>[S](f: => T => S) = new FunParser[I, T, S](p, f)

  def ~[S](q: => Parser[I, S]) = new SeqParser[I, T, S](p, q)
}

// =====================================================================
// Parse Tree Datatypes
abstract class Stmt
abstract class AExp
abstract class BExp

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Read(s: String) extends Stmt
case class WriteId(s: String) extends Stmt
case class Write(s: String) extends Stmt
case class For(i: String, a: AExp, u: AExp, bl: Block) extends Stmt

case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bopa(o: String, a1: AExp, a2: AExp) extends BExp
case class Bopb(o: String, b1: BExp, b2: BExp) extends BExp


// Arithmetic expressions
lazy val AExp: Parser[List[(String, String)], AExp] =
(Te ~ ("o", "+") ~ AExp) ==> { case ((x, y), z) => Aop("+", x, z): AExp } ||
  (Te ~ ("o", "-") ~ AExp) ==> { case ((x, y), z) => Aop("-", x, z): AExp } ||
  Te
lazy val Te: Parser[List[(String, String)], AExp] =
  (Fa ~ ("o", "*") ~ Te) ==> { case ((x, y), z) => Aop("*", x, z): AExp } ||
    (Fa ~ ("o", "%") ~ Te) ==> { case ((x, y), z) => Aop("%", x, z): AExp } ||
    (Fa ~ ("o", "/") ~ Te) ==> { case ((x, y), z) => Aop("/", x, z): AExp } ||
    Fa
lazy val Fa: Parser[List[(String, String)], AExp] =
  ("p", "(") ~ AExp ~ ("p", ")") ==> { case ((x, y), z) => y } ||
    IdParser ==> Var ||
    NumParser ==> Num

// boolean expressions (have to take Aexp or Bexp)

// maybe here ! case??
lazy val BExp: Parser[List[(String, String)], BExp] =
  (AExp ~ ("o", "==") ~ AExp) ==> { case ((x, y), z) => Bopa("==", x, z): BExp } ||
    (AExp ~ ("o", "!=") ~ AExp) ==> { case ((x, y), z) => Bopa("!=", x, z): BExp } ||
    (AExp ~ ("o", "<") ~ AExp) ==> { case ((x, y), z) => Bopa("<", x, z): BExp } ||
    (AExp ~ ("o", ">") ~ AExp) ==> { case ((x, y), z) => Bopa(">", x, z): BExp } ||
    (Re ~ ("o", "==") ~ BExp) ==> { case ((x, y), z) => Bopb("==", x, z): BExp } ||
    (Re ~ ("o", "!=") ~ BExp) ==> { case ((x, y), z) => Bopb("!=", x, z): BExp } ||
    (Re ~ ("o", "&&") ~ BExp) ==> { case ((x, y), z) => Bopb("&&", x, z): BExp } ||
    (Re ~ ("o", "||") ~ BExp) ==> { case ((x, y), z) => Bopb("||", x, z): BExp } ||
    (AExp ~ ("o", "<=") ~ AExp) ==> { case ((x, y), z) => Bopa("<=", x, z): BExp } ||
    Re
lazy val Re: Parser[List[(String, String)], BExp] =
  (("b", "true") ==> ((_) => True: BExp)) ||
    (("b", "false") ==> ((_) => False: BExp)) ||
    (("p", "(") ~ BExp ~ ("p", ")")) ==> { case ((x, y), z) => y } 
    // || ("!" ~ BExp) ==> { case (x, y) => Bopb("!", y, y): BExp }

//
// Stmts
lazy val Stmt: Parser[List[(String, String)], Stmt] =
  ("k", "skip") ==> { (_) => Skip: Stmt } ||
  (IdParser ~ ("o", ":=") ~ AExp) ==> { case ((x, y), z) => Assign(x, z): Stmt } ||
  (("k", "if") ~ BExp ~ ("k", "then") ~ Block ~ ("k", "else") ~ Block) ==> { case (((((x, y), z), u), v), w) => If(y, u, w): Stmt } ||
  (("k", "while") ~ BExp ~ ("k", "do") ~ Block) ==> { case (((x, y), z), w) => While(y, w) } ||
  (("k", "read") ~ IdParser) ==> { case (x, y) => Read(y) } ||
  (("k", "write") ~ IdParser) ==> { case (x, y) => WriteId(y)} ||
  (("k", "write") ~ StringParser) ==> { case (x, y) => Write(y)} ||
  (("k", "for") ~ IdParser ~ ("o", ":=") ~ AExp ~ ("k", "upto") ~ AExp ~ ("k", "do") ~ Block) ==> { case (((((((x, y), z), u), v), w), t), q) => For(y, u, w, q) }

lazy val Stmts: Parser[List[(String, String)], Block] =
(Stmt ~ ("s", ";") ~ Stmts) ==> { case ((x, y), z) => x :: z: Block } ||
  (Stmt ==> ((s) => List(s): Block))

lazy val Block: Parser[List[(String, String)], Block] =
  (("b", "{") ~ Stmts ~ ("b", "}")) ==> { case ((x, y), z) => y } ||
    (Stmt ==> ((s) => List(s)))

// ======================================================================================

// Interpreter
type Env = Map[String, Int]

def eval_aexp(a: AExp, env: Env): Int = a match {
  case Num(i) => i
  case Var(s) => env(s)
  case Aop("+", a1, a2) => eval_aexp(a1, env) + eval_aexp(a2, env)
  case Aop("-", a1, a2) => eval_aexp(a1, env) - eval_aexp(a2, env)
  case Aop("*", a1, a2) => eval_aexp(a1, env) * eval_aexp(a2, env)
  // new
  case Aop("/", a1, a2) => eval_aexp(a1, env) / eval_aexp(a2, env)
  case Aop("%", a1, a2) => eval_aexp(a1, env) % eval_aexp(a2, env)
}

// need two different case types because of re-use of symbols (==, !=) w/ eval'ing aexps and bexps??
def eval_bexp(b: BExp, env: Env): Boolean = b match {
  case True => true
  case False => false
  case Bopa("==", a1, a2) => eval_aexp(a1, env) == eval_aexp(a2, env)
  case Bopa("!=", a1, a2) => !(eval_aexp(a1, env) == eval_aexp(a2, env))
  case Bopa(">", a1, a2) => eval_aexp(a1, env) > eval_aexp(a2, env)
  case Bopa("<", a1, a2) => eval_aexp(a1, env) < eval_aexp(a2, env)
  // new
  case Bopb("==", b1, b2) => eval_bexp(b1, env) == eval_bexp(b2, env)
  case Bopb("!=", b1, b2) => !(eval_bexp(b1, env) == eval_bexp(b2, env))
  case Bopb("&&", b1, b2) => eval_bexp(b1, env) > eval_bexp(b2, env)
  case Bopb("||", b1, b2) => eval_bexp(b1, env) < eval_bexp(b2, env)
  case Bopa("<=", a1, a2) => eval_aexp(a1, env) <= eval_aexp(a2, env)
  // case Bopb("!", b1, b2) => !(eval_bexp(b1, env))
}

def eval_stmt(s: Stmt, env: Env): Env = s match {
  case Skip => env
  case Assign(x, a) => env + (x -> eval_aexp(a, env))
  case If(b, bl1, bl2) => if (eval_bexp(b, env)) eval_bl(bl1, env) else eval_bl(bl2, env)
  case While(b, bl) =>
    if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env))
    else env
  case Read(n) => env + (n -> scala.io.StdIn.readLine("= ").toInt)
  case Write(w) => println(w); env // no changes to the environment
  case WriteId(w) => println(env.get(w).get); env // no changes to the environment
  // new
  case For(i, a, u, bl) => { // do i even need this...
    // add i = a to the environment
    val assignenv = eval_stmt(Assign(i, a), env);
    // while loop:
    val forcondition = Bopa("<=", Var(i), u);  // i is <= the "upto" AExp
    val incrementi = Assign(i, Aop("+", Var(i), Num(1)))
    val blincrementi = bl ++ List(incrementi); // add the statement to the block????

    eval_stmt(While(forcondition, blincrementi), assignenv)
  }
}

def eval_bl(bl: Block, env: Env): Env = bl match {
  case Nil => env
  case s :: bl => eval_bl(bl, eval_stmt(s, env))
}

def eval(bl: Block): Env = eval_bl(bl, Map())


// =================================================================
// Compiler


// compiler headers needed for the JVM
// (contains an init method, as well as methods for read and write)
val beginning = """
.class public XXX.XXX
.super java/lang/Object

.method public <init>()V
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   return
.end method

.method public static write(I)V 
    .limit locals 1 
    .limit stack 2 
    getstatic java/lang/System/out Ljava/io/PrintStream; 
    iload 0
    invokevirtual java/io/PrintStream/println(I)V 
    return 
.end method

.method public static read()I 
    .limit locals 10 
    .limit stack 10

    ldc 0 
    istore 1  ; this will hold our final integer 
Label1: 
    getstatic java/lang/System/in Ljava/io/InputStream; 
    invokevirtual java/io/InputStream/read()I 
    istore 2 
    iload 2 
    ldc 10   ; the newline delimiter 
    isub 
    ifeq Label2 
    iload 2 
    ldc 32   ; the space delimiter 
    isub 
    ifeq Label2

    iload 2 
    ldc 48   ; we have our digit in ASCII, have to subtract it from 48 
    isub 
    ldc 10 
    iload 1 
    imul 
    iadd 
    istore 1 
    goto Label1 
Label2: 
    ;when we come here we have our integer computed in local variable 1 
    iload 1 
    ireturn 
.end method

.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200

"""

val ending = """

   return

.end method
"""

println("Start compilation")


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// environments and instructions
type Env = Map[String, String]
type Instrs = List[String]

// arithmetic expression compilation
//done
def compile_aexp(a: AExp, env : Env) : Instrs = a match {
  case Num(i) => List("ldc " + i.toString + "\n")
  case Var(s) => List("iload " + env(s) + "\n")
  case Aop("+", a1, a2) => 
    compile_aexp(a1, env) ++ 
    compile_aexp(a2, env) ++ List("iadd\n")
  case Aop("-", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ List("isub\n")
  case Aop("*", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ List("imul\n")
  // new
  case Aop("/", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ List("idiv\n")
  case Aop("%", a1, a2) => 
   compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ List("irem\n")
}

// boolean expression compilation
def compile_bexp(b: BExp, env : Env, jmp: String) : Instrs = b match {
  case True => Nil
  case False => List("goto " + jmp + "\n")
  case Bopa("==", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ 
    List("if_icmpne " + jmp + "\n")
  case Bopa("!=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ 
    List("if_icmpeq " + jmp + "\n")
  case Bopa("<", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ 
    List("if_icmpge " + jmp + "\n")
  //new
  case Bopa(">", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ 
    List("if_icmple " + jmp + "\n")
  case Bopa("<=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ 
    List("if_icmpgt " + jmp + "\n") // ""
}

// statement compilation
def compile_stmt(s: Stmt, env: Env) : (Instrs, Env) = s match {
  case Skip => (Nil, env)
  case Assign(x, a) => {
    val index = if (env.isDefinedAt(x)) env(x) else 
                    env.keys.size.toString
    (compile_aexp(a, env) ++ 
     List("istore " + index + "\n"), env + (x -> index))
  } 
  case If(b, bl1, bl2) => {
    val if_else = Fresh("If_else")
    val if_end = Fresh("If_end")
    val (instrs1, env1) = compile_block(bl1, env)
    val (instrs2, env2) = compile_block(bl2, env1)
    (compile_bexp(b, env, if_else) ++
     instrs1 ++
     List("goto " + if_end + "\n") ++
     List("\n" + if_else + ":\n\n") ++
     instrs2 ++
     List("\n" + if_end + ":\n\n"), env2)
  }
  case While(b, bl) => {
    val loop_begin = Fresh("Loop_begin")
    val loop_end = Fresh("Loop_end")
    val (instrs1, env1) = compile_block(bl, env)
    (List("\n" + loop_begin + ":\n\n") ++
     compile_bexp(b, env, loop_end) ++
     instrs1 ++
     List("goto " + loop_begin + "\n") ++
     List("\n" + loop_end + ":\n\n"), env1)
  }
  case WriteId(x) => 
    (List("iload " + env(x) + "\n" + 
           "invokestatic XXX/XXX/write(I)V\n"), env)
  case Read(x) => {
    val index = if (env.isDefinedAt(x)) env(x) else 
                    env.keys.size.toString
    (List("invokestatic XXX/XXX/read()I\n" + 
          "istore " + index + "\n"), env + (x -> index)) 
  }

  //new
  case Write(x) => {
    (List("ldc " + x.toString + "\n" +
           "invokestatic XXX/XXX/writes(Ljava/lang/String;)V\n"), env)
  }
  case For(i, a, u, bl) => {
     // don't allow old variables to be used here!!!
     if (env.isDefinedAt(i)) throw new Exception("No!!") else {
     
     // assign i outside of loop
     val (assignstmts, assignenv) = compile_stmt(Assign(i, a), env)

     // while loop
     val loop_begin = Fresh("Loop_begin")
     val loop_end = Fresh("Loop_end")
     val b = Bopa("<=", Var(i), u) // boolean check, i upto u
     val (blockstmts, blockenv) = compile_block(bl, assignenv) // include the assignment in the environment??

    // increment i
    val incr = Aop("+", Var(i), Num(1))
    val (incstmts, incenv) = compile_stmt(Assign(i, incr), blockenv)
     
     ( assignstmts ++
     List("\n" + loop_begin + ":\n\n") ++
     compile_bexp(b, assignenv, loop_end) ++
     blockstmts ++
     incstmts ++
     List("goto " + loop_begin + "\n") ++
     List("\n" + loop_end + ":\n\n"),
    incenv)
     }
  }
}

// compilation of a block (i.e. list of instructions)
def compile_block(bl: Block, env: Env) : (Instrs, Env) = bl match {
  case Nil => (Nil, env)
  case s::bl => {
    val (instrs1, env1) = compile_stmt(s, env)
    val (instrs2, env2) = compile_block(bl, env1)
    (instrs1 ++ instrs2, env2)
  }
}

// main compilation function for blocks
def compile(bl: Block, class_name: String) : String = {
  val instructions = compile_block(bl, Map.empty)._1
  (beginning ++ instructions.mkString ++ ending).replaceAllLiterally("XXX", class_name)
}

// Fibonacci numbers as a test-case
val fib_test = 
  List(Read("n"),                       //  read n;                     
       Assign("minus1",Num(0)),         //  minus1 := 0;
       Assign("minus2",Num(1)),         //  minus2 := 1;
       Assign("temp",Num(0)),           //  temp := 0;
       While(Bopa("<",Num(0),Var("n")),  //  while n > 0 do  {
          List(Assign("temp",Var("minus2")),    //  temp := minus2;
               Assign("minus2",Aop("+",Var("minus1"),Var("minus2"))), 
                                        //  minus2 := minus1 + minus2;
               Assign("minus1",Var("temp")), //  minus1 := temp;
               Assign("n",Aop("-",Var("n"),Num(1))))), //  n := n - 1 };
       Write("minus1"))                 //  write minus1

// prints out the JVM-assembly program

println(compile(fib_test, "fib"))

// can be assembled with 
//
//    java -jar jvm/jasmin-2.4/jasmin.jar fib.j
//    java -jar /jasmin-2.4/jasmin.jar fib.j

// and started with
//
//    java fib/fib

import scala.util._
import scala.sys.process._
import scala.io

def compile_tofile(bl: Block, class_name: String) = {
  val output = compile(bl, class_name)
  val fw = new java.io.FileWriter(class_name + ".j") 
  fw.write(output) 
  fw.close()
}

def compile_all(bl: Block, class_name: String) : Unit = {
  compile_tofile(bl, class_name)
  println("compiled ")
  val test = ("java -jar Library/jasmin-2.4/jasmin.jar " + class_name + ".j").!!
  println("assembled ")
}

def compile_run(bl: Block, class_name: String) : Unit = {
  println("Start compilation")
  compile_all(bl, class_name)
  // println("Time: " + time_needed(1, ("java " + class_name + "/" + class_name).!))
}


// compile_all(fib_test, "fib")

// ==============================================
//Q1

val fact ="""write "Factorial";
read n;
fact := 1;
while n < 0 do {
fact := n * fact;
n := n - 1
};
write "result";
write fact
"""

val factlexed = env(lexing_simp(WHILE_REGS, fact)).filterNot{_._1 == "w"}
val factparsed = (Stmts.parse_all(factlexed))
println(compile_tofile(factparsed.head, "fact"))
compile_run(factparsed.head, "while")


val fib ="""write "Fib";
read n;
minus1 := 0;
minus2 := 1;
while n > 0 do {
temp := minus2;
minus2 := minus1 + minus2;
minus1 := temp;
n := n - 1
};
write "Result";
write minus2
"""
val fiblexed = env(lexing_simp(WHILE_REGS, fib)).filterNot{_._1 == "w"}
val fibparsed = (Stmts.parse_all(fiblexed))
println(compile_tofile(fibparsed.head, "fib"))

//==============================================
// Q2

val forloop ="""for i := 2 upto 4 do {
write i
}"""

val forlexed = env(lexing_simp(WHILE_REGS, forloop)).filterNot{_._1 == "w"}
val forparsed = (Stmts.parse_all(forlexed))
println(compile(forparsed.head, "for"))

// compare instrs to...

val whileloop="""i := 2;
while (i <= 4) do {
write i;
i := i + 1
}"""

val whilelexed = env(lexing_simp(WHILE_REGS, whileloop)).filterNot{_._1 == "w"}
val whileparsed = (Stmts.parse_all(whilelexed))
println(compile(whileparsed.head, "while"))

//==============================================
// Q3

val nestedloop ="""for i := 1 upto 10 do {
for i := 1 upto 10 do {
write i
}
}"""

val nestedlexed = env(lexing_simp(WHILE_REGS, nestedloop)).filterNot{_._1 == "w"}
val nestedparsed = (Stmts.parse_all(nestedlexed))
println(compile(nestedparsed.head, "for"))