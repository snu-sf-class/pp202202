abstract class PrimesSig
{
  def prime : Int
  def getNext : PrimesSig
}

abstract class PrimesFactory
{
  def newPrimes : PrimesSig
}

def nthPrime(pf: PrimesFactory, n: Int): Int = {
  def go(primes: PrimesSig, k: Int): Int =
    if (k <= 1) primes.prime
    else go(primes.getNext, k - 1)
  if (n == 0) 2 else go(pf.newPrimes, n)
}

/* import begin */

class Primes private (val prime:Int,protected val primes:List[Int])
  extends PrimesSig
{ def this() = this(3, List(3))
  def getNext: Primes = {
    val p = computeNextPrime(prime + 2)
    new Primes(p, primes ++ (p :: Nil))
  }
  private def computeNextPrime(n: Int) : Int =
    if (primes.forall((p:Int) => n%p != 0)) n
    else computeNextPrime(n+2)
}

class PrimesImpl extends PrimesFactory {
  def newPrimes = new Primes()
}

/* import end */


nthPrime(new PrimesImpl, 10000)
