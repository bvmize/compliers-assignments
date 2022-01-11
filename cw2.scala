import scala.language.implicitConversions    
import scala.language.reflectiveCalls

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
case class Range(v: Val) extends Val
case class Optional(v: Val) extends Val
   
// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

// nullable function: tests whether the regular 
// expression can recognise the empty string
def nullable (r: Rexp) : Boolean = r match {
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

// derivative of a regular expression w.r.t. a character
def der (c: Char, r: Rexp) : Rexp = r match {
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

// derivative w.r.t. a string (iterates der)
def ders (s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, der(c, r))
}

// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
  // NEW
  case Range(v) => flatten(v)
  case Optional(v) => flatten(v)
  // Don't need values for Ntimes/Plus (use Stars)
}

// extracts an environment from a value
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
  // NEW 
  case Range(v) => env(v)
  case Optional(v) => env(v)
  // Don't need values for Ntimes/Plus (use Stars)
}

// injection part
def mkeps(r: Rexp) : Val = r match {
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

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
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

  // format of nullable PLUS(r) ders will always be nullable • STAR(r)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)

  // mkeps will always be whatever was inside the ?...
  // Ever reached by der?
  case (OPTIONAL(r), _) => Optional(inj(r, c, v))

  // format of value will always be (the match) • Stars
  case (NTIMES(r, n), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
}

// main lexing function (produces a value)
def lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) 
              else throw new Exception("Not matched")
  case c::cs => inj(r, c, lex(der(c, r), cs))
}

def lexing(r: Rexp, s: String) : Val = lex(r, s.toList)

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

// simplification of regular expressions returning also an
// rectification function; no simplification under STAR 
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
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
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
}

def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else throw new Exception("Not matched")
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) : Val = lex_simp(r, s.toList)


// Q1
//=============

def PLUS(r: Rexp) = r ~ r.%

val SYM = RANGE(('a' to 'z').toSet ++ ('A' to 'Z').toSet)
val DIGIT = RANGE(('0' to '9').toSet)
val NONZERO = RANGE(('1' to '9').toSet)

//1
val KEYWORD : Rexp = "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false"| "read" | "write" | "skip"
//2
val OP: Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | ":=" | "&&" | "||" 
//3
val STRING: Rexp = """"""" ~ SYM.% ~ """""""
//4
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val LCURLYBRACE: Rexp = "{"
val RCURLYBRACE: Rexp = "}"
//5
val SEMI: Rexp = ";"
//6
val WHITESPACE = PLUS(" " | "\n" | "\t")
//7
val ID = SYM ~ ("_" | SYM | DIGIT).% 
//8
val NUM = "0" | NONZERO ~ DIGIT.%

val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("i" $ ID) | 
                  ("o" $ OP) | 
                  ("n" $ NUM) | 
                  ("s" $ SEMI) | 
                  ("str" $ STRING) |
                  ("p" $ (LPAREN | RPAREN)) | 
                  ("b" $ (LCURLYBRACE | RCURLYBRACE)) | 
                  ("w" $ WHITESPACE)).%

// Q2
//=============
lexing(NTIMES("a", 3), "aaa")
lexing(PLUS(("a" | ONE)), "aa")
lexing(STAR(("a")), "")

val prog0 = """read n;"""
println(env(lexing(WHILE_REGS, prog0)))

// Q3
//=============

val fib = """
write "fib";
read n;
minus1 := 0;
minus2 := 1;
while n > 0 do {
  temp := minus2;
  minus2 := minus1 + minus2;
  minus1 := temp;
  n := n - 1
};
write "result";
write minus2
"""

println("Fib Tokens")
println(env(lexing_simp(WHILE_REGS, fib)))
println(env(lexing_simp(WHILE_REGS, fib)).filterNot{_._1 == "w"}.mkString("\n"))

val nestedloops = """
start := 1000;
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
}
"""
println("Three Nested Loops Tokens")
println(env(lexing_simp(WHILE_REGS, nestedloops)))
println(env(lexing_simp(WHILE_REGS, nestedloops)).filterNot{_._1 == "w"}.mkString("\n"))


// some more timing tests with
// i copies of the program

def time[T](code: => T) = {
  val start = System.nanoTime()
  val result = code
  val end = System.nanoTime()
  println((end - start)/1.0e9)
  result
}

for (i <- 1 to 21 by 10) {
  print(i.toString + ":  ")
  time(lexing_simp(WHILE_REGS, fib * i))
}
for (i <- 1 to 21 by 10) {
  print(i.toString + ":  ")
  time(lexing_simp(WHILE_REGS, nestedloops * i))
}

// Heap space error in the non-simp!!
for (i <- 1 to 21 by 10) {
  print(i.toString + ":  ")
  time(lexing(WHILE_REGS, fib * i))
}

// More Testing
// ===================

// plus
val foo = der('a', PLUS("a"))
val bar = mkeps(foo)
inj(PLUS("a"), 'a', bar)

val baz = der('a', PLUS("a" | "b"))
val qux = mkeps(baz)
inj(PLUS("a" | "b"), 'a', qux)

lexing(PLUS("a"), "aaa")
lexing(PLUS("aaaa"), "a")
lexing(PLUS("a" | "b"), "abbb")
lexing(PLUS("a" | ONE), "aaaa")
lexing(PLUS("a" | ONE), "")
lexing(PLUS("a"), "aac")

// Optional
val foo = der('a', OPTIONAL("a"))
val bar = mkeps(foo)
inj(OPTIONAL("a"), 'a', bar)

val baz = der('a', OPTIONAL("a" | "b"))
val qux = mkeps(baz)
inj(OPTIONAL("a" | "b"), 'a', qux)

lexing(OPTIONAL("a"), "aaa")
lexing(OPTIONAL("a"), "a") 
lexing(OPTIONAL("a"), "")
lexing(OPTIONAL("a" | "b"), "a") 
lexing(OPTIONAL("a" | ""), "") 
lexing(OPTIONAL("a"), "aac")

// Ntimes
val hey = der('a', NTIMES("a", 1))
val you = mkeps(hey)
inj(NTIMES("a", 1), 'a', you)

val foobar = der('a', NTIMES(("a" | "b"), 1))
val barbaz = mkeps(foobar)
inj(NTIMES(("a" | "b"), 1), 'a', barbaz)

lexing(NTIMES("a", 1), "aaa")
lexing(NTIMES("a", 3), "aaa")
lexing(NTIMES(("a" | "b"), 3), "abb") 
lexing(NTIMES(("a" | ONE), 1), "")
lexing(NTIMES("a", 1), "c")