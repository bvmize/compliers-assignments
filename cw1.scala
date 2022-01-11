
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
// new
case class RANGE(cs: Set[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp 
case class UPTO(r: Rexp, m: Int) extends Rexp 
case class FROM(r: Rexp, n: Int) extends Rexp
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp
case class NOTR(r: Rexp) extends Rexp
//Q3
case object ALL extends Rexp 
case class CFUN(c: Char => Boolean) extends Rexp

// nullable function: tests whether the regular 
// expression can recognize the empty string
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  //new
  case RANGE(chars) => false
  case PLUS(r) => nullable(r)
  case OPTIONAL(_) => true
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  case UPTO(r, n) => true
  case FROM(r, i) => if (i == 0) true else nullable(r)
  case BETWEEN(r, n, m) => if (n == 0) true else nullable(r)
  case NOTR(r) => !(nullable(r))

  // ?
  case ALL => false
  case CFUN(_) => false
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
  case STAR(r1) => SEQ(der(c, r1), STAR(r1))

  //new
  case RANGE(chars) => 
      if (chars(c)) ONE
      else ZERO
  case PLUS(r) =>
      // if (nullable(r)) ALT(SEQ(der(c, r), STAR(r)), der(c, STAR(r)))
      // else (SEQ(der(c, r), STAR(r)))
      SEQ(der(c, r), STAR(r))
  case OPTIONAL(r) => der(c, r) 
  case NTIMES(r, i) => 
     if (i == 0) ZERO 
     else SEQ(der(c, r), NTIMES(r, i - 1))
  case UPTO(r, i) => 
     if (i == 0) ZERO
     else SEQ(der(c, r), UPTO(r, i - 1)) 
  case NOTR(r) => NOTR(der(c, r)) 
  case CFUN(f) => 
     if (f(c)) ONE
     else ZERO
 case FROM(r, i) => 
     if (i == 0) SEQ(der(c, r), STAR(r))
     else SEQ(der(c, r), FROM(r, i - 1))
 case BETWEEN(r, i, j) => 
     if (i == 0 && j == 0) ZERO else
     if (i == 0 && j > 0) SEQ(der(c, r), UPTO(r, j - 1)) 
     else SEQ(der(c, r), BETWEEN(r, i - 1, j - 1))
  case ALL => ONE
}

// simplification
def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case r => r
}

// derivative w.r.t. a string (iterates der)
def ders (s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  // case c::s => ders(s, simp(der(c, r)))
  case c::s => ders(s, der(c, r))
}

// matcher function
def matcher(r: Rexp, s: String) : Boolean = nullable(ders(s.toList, r))

//regular to test
val AFROM3 = FROM(CHAR('a'), 3)
val AOPT3 = NTIMES(OPTIONAL(CHAR('a')), 3)
val AUPTO3 = UPTO(CHAR('a'), 3)
val AOPTUPTO3 = UPTO(OPTIONAL(CHAR('a')), 3)
val ABTWNN35 = BETWEEN((CHAR('a')), 3, 5)
val AOPTBTWN35 = BETWEEN(OPTIONAL(CHAR('a')), 3, 5)
val AOPT = OPTIONAL(CHAR('a'))
val AORONE = ALT(CHAR('a'), ONE)
val AORONEBTWNN35 = BETWEEN((AORONE), 3, 5)

//test cases
val as = Array("", "a", "aa", "aaa", "aaaa","aaaaa", "aaaaaaaaaaaa")
val arexps = Array(AFROM3, AOPT3, AUPTO3, AOPTUPTO3, ABTWNN35, AOPTBTWN35, AOPT, AORONE, AORONEBTWNN35)

//Q3 Test
for (i <- 0 to 8) {
  println("\n" +arexps(i))
  for (j <- 0 to 6) {
    println(as(j) + ": " + matcher(arexps(i), as(j)))
  }
}


//Q5
// regex
val validchars = ('0' to '9').toSet ++ ('a' to 'z').toSet ++ Set('_', '.', '-')
val ADDRESS = PLUS(RANGE(validchars))
val DOMAINNAME = PLUS(RANGE(validchars - '_'))
val TOPLEVELDOMAIN = BETWEEN(RANGE(('a' to 'z').toSet ++ Set('.')), 2, 6)
val EMAIL = SEQ(SEQ(SEQ(SEQ(ADDRESS, CHAR('@')), DOMAINNAME), CHAR('.')), TOPLEVELDOMAIN)

// test
matcher(EMAIL, "k1781405@kcl.ac.uk")
ders("a".toList, PLUS(ALT(CHAR('a'), CHAR('b'))    )


//other tests
val tests = List("k1781405.", "k1781405-", "k1781405_", "k1781405@kcl", "k1781405@kcl.ac.uk", 
                  "k1781405@kcl.", "kcl.ac", ".uk")

for (i <- 0 to 7) {
  println("ADDRESS matches " + tests(i) + "? : " + matcher(ADDRESS, tests(i)))
}
// true, true, true, false, false, false, true, true

for (i <- 0 to 7) {
  println("DOMAINNAME matches " + tests(i) + "? : " + matcher(DOMAINNAME, tests(i)))
}
// true, true, false, false, false, false, true, true

for (i <- 0 to 7) {
  println("TOPLEVELDOMAIN matches " + tests(i) + "? : " + matcher(TOPLEVELDOMAIN, tests(i)))
}
// false, false, false, false, false, false, true, true

for (i <- 0 to 7) {
  println("EMAIL matches " + tests(i) + "? : " + matcher(EMAIL, tests(i)))
}
// only matches k1781405@kcl.ac.uk


// Q6 
//regex
val START = SEQ(CHAR('/'), CHAR('*'))
val END = SEQ(CHAR('*'), CHAR('/'))
val BODY = NOTR(SEQ(SEQ(STAR(ALL), END), STAR(ALL)))
val COMMENT = SEQ(SEQ(START, BODY), END)

//test
val comments = Array("/**/", "/*foobar*/", "/*test*/test*/", "/*test/*test*/")
for (i <- 0 to 3) {
  println((i + 1) + ": " + matcher(COMMENT, comments(i)))
}
//true, true, false, true

// Q7
val r1 = SEQ(SEQ(CHAR('a'), CHAR('a')), CHAR('a'))
val r2 = SEQ(NTIMES(CHAR('a'), 19), OPTIONAL(CHAR('a'))) // 19 or 20 as

//test
//120, 131, 136
val lotsofas = Array("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
 "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")

// val manyas = Array("a" * 120, "a" * 131, "a"*136)

for (i <- 0 to 2) {
  println(lotsofas(i).length + ": " + matcher(PLUS(PLUS(r1)), lotsofas(i))) // multiples of 3
} 
// true, false, false

for (i <- 0 to 2) {
  println(lotsofas(i).length + ": " + matcher(PLUS(PLUS(r2)), lotsofas(i))) // multiples of 19 & 20??
} 
// true, false, true
