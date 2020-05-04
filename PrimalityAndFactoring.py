import math
import random

#This File contains various number theoretic scripts I used when teaching Intro number Theory in Spring 2020

#MillerRabin(n,T) performs T trials of the Miller-Rabin Primality Test.  We pick a random base a. and check to make sure a^(n-1)=1 mod n, and also that all square roots that are easy to compute (a^((n-1)/2^k) mod n) return what they ought to (i.e. we compute a^(n-1)/2^k while 2^k divides n-1.  If we ever see a square root of 1 other than +/-1 we call foul.  
#It also computes the probability that a is prime assuming a random number of size n is prime with probability 1/log(n).  We use the worst case estimate that Miller-Rabin detects composites with probability >=3/4.
def MillerRabin(n,T):
    twos = TwoFactorer(n-1)
    for t in range(T):
        a = random.randint(1,n-2)
        twos = TwoFactorer(n-1)
        current = pow(a,twos[0],n)
        if current ==1:
            continue
        for k in range(twos[1]):
            prior = current
            current = pow(current,2,n)
            if current==1:
                if prior-n==-1:
                    break
                else:
                    print("{} fails the Miller Rabin test with base {}.  Check the {}th power".format(n,a,k))
                    return(False)
        if current !=1:
            print("{} fails Fermat primality test with base {}.".format(n,a))
            return(False)
    print("{} Passed {} rounds of the Miller-Rabin test.\nIt is prime with probability {}".format(n,T,1/(pow(4,-T)*(math.log(n)-1)+1)))
    return(True)

#SolovayStrassen(n,T) performs T trials of the Solovay Strassen primality test on n.  It checks for random inputs if the jacobi symbol (a|n) equals Euler's Criterion a^(n-1)/2 mod n.  It also computes the probability that a is prime assuming a random number of size n is prime with probability 1/log(n).  We use the worst case estimate that Solovay Strassen detects composites with probability >=1/2.
def SolovayStrassen(n,T):
    euler_criterion = (n-1)//2
    for t in range(T):
        a = random.randint(1,n-2)
        if pow(a,euler_criterion,n)!=Jacobi(a,n)%n:
            print("{number} fails the Solovay Strassen Test for base {base}".format(number= n, base = a))
            return(False)
    print("{} passed {} trials of the Solovay Strassen primality test.  \nThe probability that it is prime is at least {}".format(n, T, 1/(pow(2,-T)*(math.log(n)-1)+1)))
    return(True)


    
#TwoFactorer(n) Returns the odd part of n, and the multiplicity to which 2 divides n.
def TwoFactorer(n):
    count = 0
    while(True):
        if n%2 !=0:
            return([n,count])
        n//=2
        count +=1    
    
    
#Jacobi(n,m) returns the Jacobi Symbol (n | m).  We use the Euclidean Algorithm-esque approach built on Reciprocity for Jacobi Symbols.  This is done by recusively removing the even parts of n and noting (2 | m)=(-1)^((m^2-1)/8).  For the odd parts we use
#Jacobi reciprocity to reduce the problem to (m | n) (-1)^((n^2-1)/4*(m^2-1)/4) and reduce m mod n to reduce our inputs.
# We split the program off into a helper program so that our recursive call doesn't repeatedly check if the inputs are coprime.
 
def Jacobi(n,m):
    if math.gcd(n,m)!=1:
        return(0)
    return(JacobiHelper(n,m))

def JacobiHelper(n,m):
    n = n%m
    twos = TwoFactorer(n)
    switcher = {
        1: 1,
        3: -1,
        5: -1,
        7: 1
        }
 
    if twos[1]%2 == 0:
        even_term = 1
    else:
        even_term = switcher.get(m%8)

    if twos[0]==1:
        return(even_term)
    elif twos[0]%4 ==3 and m%4 ==3:
        return(-even_term*JacobiHelper(m,twos[0]))
    else:
        return(even_term*JacobiHelper(m,twos[0]))
    
    

#



#LucasLehmer(n) uses the Lucas Lehmer test to test primality of 
#the nth Mersenne Prime
def LucasLehmer(n):
    N = 2**n-1
    u = 4
    for i in range(n-2):
        u = pow(u,2,N)-2
    u=u%N
    if u==0:
        print("The %d th Mersenne Number %d is prime"%(n,N))
        return(True)
    else:
        print("The %d th Mersenne Number %d is notprime.  u%d=%d"%(n,N,n-2,u))
        return(False)

#Pepin(n) checks the primality of the nth Fermat number 2^(2^n)+1
#using Pepin's test.

def Pepin(n):
    Fn = pow(2,pow(2,n))+1
    if pow(3,2**n-1,Fn)==Fn-1:
        print("The %d th Fermat Number %d is prime"%(n,Fn))
        return(True)
    else:
        print("The %d th Fermat Number %d is not prime."%(n,Fn))
        return(True)

    

#PollardRhoFermat is a specialized implementation of the Pollard
#Rho Algorithm for factoring Fermat numbers, as recommended
#by Brent and Pollard in their Factorization of F_8

def PollardRhoFermat(k,T):
    n = pow(2,pow(2,k))+1
    f = lambda x: pow(x,pow(2,k+2), n)+1 % n
    x = 3
    y = 3
    for i in range(T):
        x = f(f(x))
        y = f(y)
        d = math.gcd(x-y, n )
        if (1<d and d<n):
            return d
    return(0)   
            
#PollardRho(n,T) tries to factor n for T steps of the Pollard Rho factoring algorithm.  It returns a nontrivial factor if it finds one, else it returns 0
def PollardRho(n,T):
    f = lambda x: pow(x,2, n)+1 % n
    x = 2
    y = 2
    count = 0
    for i in range(T):
        count+=1
        x = f(f(x))
        y = f(y)
        d = math.gcd(x-y, n )
        if (1<d and d<n):
            print("The factoring took {} steps".format(count))
            return d
    return(0)   

#PollardPMinusOne(n,b) attempts to factor n using Pollard p-1 factorizaton  with a smoothness bound of b.  It will work if the order of 2 has all prime power factors less than b.  Upon failure it will return 1.  On success, it will return a prime factor.
#An optional input base let's you use bases other than 2.
#Another optional how_smooth flag tells the algorithm to tell
#what primes it needed to consider.
def PollardPMinusOne(n,b,base=2,how_smooth=False):
    B = SieveOfEratosthenes(b)
    current = base
    #We we hope 2^L=1 mod q where L is the product over all primes of the largest prime power less than the smoothness bound B.  We compute this exponention one prime at a time.   at the end current will be 2^L
    #We succeed if for some prime divisor q of n-1 the order of 2 mod q is B smooth.
    #we check the gcd at each step lest we miss our window
    #A more efficient implementation might check gcds less often and backtrack to look for nontrivial factors
    for p in B:
        prime_power = p
        while(prime_power<=b):
            current= pow(current, p, n)
            prime_power*=p
            if math.gcd(current-1,n)!=1:
                if how_smooth:
                    print("We checked primes up to {}".format(p))
                return(math.gcd(current-1,n))
    return(math.gcd(current-1,n))
    
    
    
    
    
    
    
#SieveOfEratosthenes(B) returns a list of all primes less than B using the classic Sieve of Eratosthenes.
def SieveOfEratosthenes(B):
    Primes=[2]
    CheckArray=[True]*(B+1)
    for n in range(4,B+1,2):
        CheckArray[n]=False
    for d in range(3,math.floor(math.sqrt(B))+1):
        if CheckArray[d]:   
            for n in range(2*d,B+1,d):
                CheckArray[n]=False
            Primes.append(d)
    for n in range(math.floor(math.sqrt(B))+1,B+1):
        if CheckArray[n]:
            Primes.append(n)
    return(Primes)