import scala.language.implicitConversions
  import scala.language.reflectiveCalls

  //========================
  // LEXER (CW2)
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

  // some convenience for typing in regular expressions
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

  val KEYWORD: Rexp = "while" | "do" | "if" | "then" | "else" | "true" | "false" | "read" | "write" | "skip"
  val OP: Rexp = "+" | "-" | "*" | "%" | "/" | "=" | "!=" | ">" | "<" | ":=" | "&&" | "||"
  val STRING: Rexp = """"""" ~ SYM.% ~ """""""
  val RPAREN: Rexp = ")"
  val LPAREN: Rexp = "("
  val LCURLYBRACE: Rexp = "{"
  val RCURLYBRACE: Rexp = "}"
  val SEMI: Rexp = ";"
  val WHITESPACE = PLUS(" " | "\n" | "\t")
  val ID = SYM ~ ("_" | SYM | DIGIT).%
  val NUM = "0" | NONZERO ~ DIGIT.%

  // val START = SEQ(CHAR('/'), CHAR('*'))
  // val END = SEQ(CHAR('*'), CHAR('/'))
  // val BODY = ~(SEQ(SEQ(STAR(ALL), END), STAR(ALL)))
  // val COMMENT = SEQ(SEQ(START, BODY), END)

  val WHILE_REGS = (("k" $ KEYWORD) |
    ("i" $ ID) |
    ("o" $ OP) |
    ("n" $ NUM) |
    ("s" $ SEMI) |
    ("str" $ STRING) |
    ("p" $ (LPAREN | RPAREN)) |
    ("b" $ (LCURLYBRACE | RCURLYBRACE)) |
    ("w" $ WHITESPACE)
    // ("c" $ COMMENT)
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

  // implicit def string2parser(s: String) = StringParser(s)


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

  //  implicit def StringOps(s: String) = new {
  //    def ||(q: => Parser[String, String]) = new AltParser[String, String](s, q)
  //
  //    def ||(r: String) = new AltParser[String, String](s, r)
  //
  //    def ==>[S](f: => String => S) = new FunParser[String, String, S](s, f)
  //
  //    def ~[S](q: => Parser[String, S]) =
  //      new SeqParser[String, String, S](s, q)
  //
  //    def ~(r: String) =
  //      new SeqParser[String, String, String](s, r)
  //  }

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

  case class Var(s: String) extends AExp

  case class Num(i: Int) extends AExp

  case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

  case object True extends BExp

  case object False extends BExp

  case class Bopa(o: String, a1: AExp, a2: AExp) extends BExp

  case class Bopb(o: String, b1: BExp, b2: BExp) extends BExp

  //=====================================================================================
  //Q1


  // Arithmetic expressions
  // list string stirng
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
  lazy val BExp: Parser[List[(String, String)], BExp] =
    (AExp ~ ("o", "==") ~ AExp) ==> { case ((x, y), z) => Bopa("==", x, z): BExp } ||
      (AExp ~ ("o", "!=") ~ AExp) ==> { case ((x, y), z) => Bopa("!=", x, z): BExp } ||
      (AExp ~ ("o", "<") ~ AExp) ==> { case ((x, y), z) => Bopa("<", x, z): BExp } ||
      (AExp ~ ("o", ">") ~ AExp) ==> { case ((x, y), z) => Bopa(">", x, z): BExp } ||
      (Re ~ ("o", "==") ~ BExp) ==> { case ((x, y), z) => Bopb("==", x, z): BExp } ||
      (Re ~ ("o", "!=") ~ BExp) ==> { case ((x, y), z) => Bopb("!=", x, z): BExp } ||
      (Re ~ ("o", "&&") ~ BExp) ==> { case ((x, y), z) => Bopb("&&", x, z): BExp } ||
      (Re ~ ("o", "||") ~ BExp) ==> { case ((x, y), z) => Bopb("||", x, z): BExp } ||
      Re
  lazy val Re: Parser[List[(String, String)], BExp] =
    (("b", "true") ==> ((_) => True: BExp)) ||
      (("b", "false") ==> ((_) => False: BExp)) ||
      (("p", "(") ~ BExp ~ ("p", ")")) ==> { case ((x, y), z) => y }
  //("!" ~ BExp) ==> { case (x, y) => Bopb("!", y, y): BExp }


  lazy val Stmt: Parser[List[(String, String)], Stmt] =
    ("k", "skip") ==> { (_) => Skip: Stmt } ||
      (IdParser ~ ("o", ":=") ~ AExp) ==> { case ((x, y), z) => Assign(x, z): Stmt } ||
      (("k", "if") ~ BExp ~ ("k", "then") ~ Block ~ ("k", "else") ~ Block) ==> { case (((((x, y), z), u), v), w) => If(y, u, w): Stmt } ||
      (("k", "while") ~ BExp ~ ("k", "do") ~ Block) ==> { case (((x, y), z), w) => While(y, w) } ||
      (("k", "read") ~ IdParser) ==> { case (x, y) => Read(y) } ||
      (("k", "write") ~ IdParser) ==> { case (x, y) => WriteId(y)} ||
      (("k", "write") ~ StringParser) ==> { case (x, y) => Write(y)}

  // starting symbol
  // Put the filters here
  //.filterNot{_._1 == "c"}
  //.filterNot{_._1 == "w"}
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
    case Bopb("!", b1, b2) => !(eval_bexp(b1, env))
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

  }

  def eval_bl(bl: Block, env: Env): Env = bl match {
    case Nil => env
    case s :: bl => eval_bl(bl, eval_stmt(s, env))
  }

  def eval(bl: Block): Env = eval_bl(bl, Map())


  //def eval(stmts: Stmts) : Env = eval_bl(bl, Map())


  //==========================================================================
  // Q2
  val q2 = "if (a < b) then skip else a := a * b + 1"
  val q2lexed = env(lexing_simp(WHILE_REGS, q2)).filterNot{_._1 == "w"}
  println(Stmts.parse_all(q2lexed))

  //====================================================================
  //Q3

  val fib =
    """write "Fib";
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
write minus2"""
  val fiblexed = env(lexing_simp(WHILE_REGS, fib)).filterNot{_._1 == "w"}
//  println(Stmts.parse_all(fiblexed))
//  println(eval(Stmts.parse_all(fiblexed).head))

val loops100 ="""start := 100;
 x := start;
 y := start;
 z := start;
 while 0 < x do {
 while 0 < y do {
 while 0 < z do { z := z - 1 };
 z := start;
 y := y - 1
 };
 y := start;
 x := x - 1
 }"""

  val loops500 ="""start := 500;
 x := start;
 y := start;
 z := start;
 while 0 < x do {
 while 0 < y do {
 while 0 < z do { z := z - 1 };
 z := start;
 y := y - 1
 };
 y := start;
 x := x - 1
 }"""

  val loops1000 ="""start := 1000;
 x := start;
 y := start;
 z := start;
 while 0 < x do {
 while 0 < y do {
 while 0 < z do { z := z - 1 };
 z := start;
 y := y - 1
 };
 y := start;
 x := x - 1
 }"""

  val loops800 ="""start := 800;
 x := start;
 y := start;
 z := start;
 while 0 < x do {
 while 0 < y do {
 while 0 < z do { z := z - 1 };
 z := start;
 y := y - 1
 };
 y := start;
 x := x - 1
 }"""

  val loops100lexed = env(lexing_simp(WHILE_REGS, loops100)).filterNot{_._1 == "w"}
  val loops500lexed = env(lexing_simp(WHILE_REGS, loops500)).filterNot{_._1 == "w"}
  val loops1000lexed = env(lexing_simp(WHILE_REGS, loops1000)).filterNot{_._1 == "w"}
  val loops800lexed = env(lexing_simp(WHILE_REGS, loops800)).filterNot{_._1 == "w"}


  def time[T](code: => T) = {
  val start = System.nanoTime()
  val result = code
  val end = System.nanoTime()
  println((end - start) / 1.0e9)
  result
}

 // time(eval(Stmts.parse_all(loops100lexed).head))
  //time(eval(Stmts.parse_all(loops500lexed).head))
  //time(eval(Stmts.parse_all(loops1000lexed).head))
 // time(eval(Stmts.parse_all(loops800lexed).head))
