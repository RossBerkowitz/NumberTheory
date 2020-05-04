# This file contains code for a (nearly from scratch) implementation of the Quadratic Sieve for factoring large integers.
#In order to solve the requisite linear system over F_2, sage is imported, and so is required to run the sieve here.



import math
import itertools
from sage.all import *
import numpy
import time

#QS(n,b,M) is the main algorithm of this file and it uses the quadratic sieve to try to find a nontrivial factor of n.  It takes as inputs the number n to be factored, a desired smoothness bound b, and a parameter M which determines how many numbers we try to sieve.  The 2M+1 smallest outputs of the function x^2-n are then sieved in search of b-smooth numbers (numbers whos prime divisors are all less than b).  After the smooth numbers are found, searching for a product of them which is a perfect square is equivalent to solving a linear system over F_2, and we use sage to solve this linear system.  If a nontrivial factor is found, the algorithm returns that factor, otherwise it sends back a message and returns 0.
#The user must make a choice of smoothness bound b and parameter M governing how big the sieve is.  Larger choices are more likely to factor properly, but also cause the sieve to run more slowly.
#There are two optional boolean inputs relation_data and speed_test
#relation_data tells the program to also print the congruence of squares it found.
#speed_test measures how much time has passed at various steps in the factoring.


def QS(n,M,b,relation_data=False,speed_test = False):
    if speed_test:
        start_time=time.process_time()
    
    #First we prepare our list of smooth primes to consider
    B = BMaker(n,b)    
    smooth_factors = len(B)
    if speed_test:
        print("After %f seconds we have our factor base" %(time.process_time()-start_time))
        
    #Next we sieve for candidate numbers which might satisfy that x^2-n is b-smooth    
    Candidates = SmoothSieve(n,M,B)
    if speed_test:
        print("After %f seconds we have our Candidate Smooth Numbers" %(time.process_time()-start_time))
    Relations = []
    #Now that we have found our candidates, we check each in turn to see if it is in fact smooth.
    for candidate in Candidates:
        temp = SmoothTrialDivision(candidate**2-n,B)
        if temp[0]:
            Relations.append([candidate,temp[1]])
    if speed_test:
        print("After %f seconds we have found our smooth numbers" %(time.process_time()-start_time))
    #Once we have our smooth numbers, we call sage to try to find a nontrivial product of them which will yield a congruence of squares    
    if len(Relations)>0:
        R = len(Relations)
        M = [Rel[1] for Rel in Relations]
        A = matrix(GF(2),M)
        if speed_test:
            print("After %f seconds we have enough relations and are ready to find a congruence of squares" %(time.process_time()-start_time))
        Ker = A.kernel()
        if speed_test:
            print("After %f seconds we found our Kernel and are going to test for nontrivial relations" %(time.process_time()-start_time))
        for attempt in range(1,Ker.dimension()+1):
            #For each relation in the Kernel, we check if the congruence of squares it gives is a trivial factor, or a nontrivial factor
            
            Hope = A.left_kernel()[attempt]
            SquareOne = 1
            for i in range(R):
                if Hope[i] == 1:
                    SquareOne = SquareOne*Relations[i][0] %n
        
            MM = [0]*(smooth_factors)
            for j in range(R):
                if Hope[j]==1:
                    for i in range(smooth_factors):
                        MM[i]+=M[j][i]
            SquareTwo = 1
            for i in range(smooth_factors):
                SquareTwo*=pow(B[i],MM[i]//2)

            Answer = math.gcd(SquareOne+SquareTwo,n)

            if Answer !=1 and Answer !=n:
                if relation_data:
                    print("%d and %d have contruent squares mod %d"%(SquareOne,SquareTwo,n))
                if speed_test:
                    print("This factoring took %f seconds to complete" %( time.process_time()-start_time))
                return(Answer)
        
        print("Bad Luck! We found {} smooth squares but didn't find any nontrivial relations".format(len(Relations)))
        return(0)
        
    if speed_test:
            print("This factoring took %f seconds to complete" %( time.process_time()-start_time))
    print("Bad Luck! We found {} smooth squares but didn't find any nontrivial relations".format(len(Relations)))
    return(0)


#NonResidueFinder(p) checks the integers mod p in order and finds the least quadratic nonresidue using Euler's Criterion.  Primality of p is assumed.
def NonResidueFinder(p):
    q = (p-1)//2
    for i in range(2,p):
        if pow(i,q,p) != 1:
            return(i)

#TwoFactorer(n) Returns the odd part of n, and the multiplicity to which 2 divides n.
def TwoFactorer(n):
    count = 0
    while(True):
        if n%2 !=0:
            return([n,count])
        n//=2
        count +=1


#BMaker returns a list of all primes p so that n is a residue mod p and n<b.  This provides our factor base for the Quadratic Sieve.
def BMaker(n,b):
    B=SieveOfEratosthenes(b)
    L = []
    for p in B:
        if pow(n,(p-1)//2,p)==1:
            L.append(p)
    return(L)

#TonelliShanks implements the Tonelli Shanks algorithm to find a solution to the equation x^2=n mod p.  Primality of p is assumed.  An error check is made
#to ensure that n is a quadratic residue mod p.  - In future versions this check should be removed as the the Quadratic Sieve will never feed it a prime p so that
# n is a nonresidue.

def TonelliShanks(n,p):
    if p==2:
        return(n%2)
    if n%p == 0:
        return(0)
    if pow(n,(p-1)//2,p) != 1:
        return('Error, not a quadratic resuide')
    temp = TwoFactorer(p-1)
    Q = temp[0]
    k = temp[1]
    b = pow(NonResidueFinder(p),Q,p)
    guess = pow(n,(Q+1)//2,p)
    current = pow(n,Q,p)
    for i in range(k-2,-1,-1):
        if pow(current,pow(2,i),p)!=1:
            guess =guess*b % p
            b = pow(b,2,p)
            current = current*b % p
        else:
            b=pow(b,2,p)
    return(guess)
    
#PPSqrt(n,p,k) finds the square roots of n mod p,p^2,...,p^k.  p is assumed to be an odd prime (for p=2 use TPSqrt), as is the fact that n is a residue mod p.
# The outputs are returned as a list of length k+1, with the first entry in the list always 0.
# The algorithm uses Tonelli Shanks to solve the equation mod p, then Hensel's Lifting lemma to lift it all the way on up to mod p^k
#For convenience, it simply returns the square roots (up to plus minus) mod p^l for l =1,2,..k in a list (the 0th entry of the list is always 0 for easy indexing)

def PPSqrt(n,p,k):    
    if n% p == 0:
        return("Error, we didn't implement the zero case yet")
    s = TonelliShanks(n,p)
    L=[0,s]
    for l in range(2,k+1):
        L.append((L[-1]-(pow(L[-1],2)-n)* pow(2*L[-1],p-2,p))% pow(p,l))
    return(L)
    
#TPSqrt(n,k) finds the square roots of n mod 2^k.
# The outputs are returned as a list of length k+1, with the first entry in the list always 0.

def TPSqrt(n,k):
    if k==1:
        return([0,[n%2]])
    switcher = {
        0: [0,[0],[0,2]],
        1: [0,[1],[1,3]],
        2: [0,[0],[]],
        3: [0,[1],[]]
        }
    L=switcher.get(n%4,"oops, Error in TPSqrt")
    for l in range(3,k+1):
        flag = True
        if L[l-1]==[]:
            L.append([])
            continue
        for x in L[l-1]:
            N = pow(2,l)
            if pow(x,2,N)==n%N:
                flag = False
                if 2*x ==N//2:
                    L.append([x,x+N//2])
                    
                else:
                    L.append([x,x+N//2,-x %N, (-x-N//2) % N])
                break
        if flag:
            L.append([])
    return(L)


#SieveOfEratosthenes(B) returns a list of all primes less than B using the classic Sieve of Eratosthenes.
def SieveOfEratosthenes(B):
    Primes=[2]
    CheckArray=[True]*(B)
    for n in range(2,B,2):
        CheckArray[n]=False
    for d in range(3,math.floor(math.sqrt(B))+1):
        if CheckArray[d]:   
            for n in range(0,B,d):
                CheckArray[n]=False
            Primes.append(d)
    for n in range(math.floor(math.sqrt(B))+1,B):
        if CheckArray[n]:
            Primes.append(n)
    return(Primes)
    



#Smooth Sieve is the key algorithmic step in the Quadratic sieve
#SmoothSieve takes inputs n, M, B and generates a string of length 2M+1 detailing which numbers x in the range [-M,M] have
#(x+[sqrt(M)])^2-N with many factors in the factor base B.
#Note, for reasons of speed this algorithm isn't exact, and only counts the number of bits of primes dividing any particular candidate.  A more rigorous check is afterwards done on the smaller list of candidates that pass this sieve.
#Note, this doesn't check that n is a residue mod p for p in B. The wrapper QS program should already have done so
    
def SmoothSieve(n,M,B):
    start_time=time.process_time()
    CheckArray = [0]*(2*M+1)
    sqrtn = math.floor(math.sqrt(n))

    start = 0
#    Smoothness = B[-1]
    # FOR TESTING FOR NOW WE ARE CHECKING LUDICROUSLY
    #HIGH PRIME POWERS.  IF IT'S SLOW WE'LL TAKE IT OUT
    Smoothness = n


    if B[0]==2:
        start = 1
        k = n.bit_length()
        S = TPSqrt(n,k)
        for l in range(1,k+1):
            for root in S[l]:
                for x in range((root-sqrtn+M)%pow(2,l),2*M+1,pow(2,l)):
                    CheckArray[x]+=1
    for p in B[start:]:
        l = p.bit_length()
        k = disclog(n,p)
        L= PPSqrt(n,p,k)
        for m in range(1,k+1):
            s = L[m]
            Step= pow(p,m)
            for x in range((s-sqrtn+M)%Step, 2*M+1,Step):
                CheckArray[x]+=l
            for x in range((-s-sqrtn+M)%Step, 2*M+1,Step):
                CheckArray[x]+=l
    Candidates = []
    for x in range(0,2*M+1):
        
        if (pow(x+sqrtn-M,2)-n).bit_length()<=CheckArray[x]:
            Candidates.append(x+sqrtn-M)
    return(Candidates)

    

#SmoothSieve_test was a test version of SmoothSieve which ignored checking prime powers.  It is faster than SmoothSieve, but missed too many smooth numbers.  At some point I intend to try allowing alternate smoothness bounds 
def SmoothSieve_test(n,M,B):
    CheckArray = [0]*(2*M+1)
    sqrtn = math.floor(math.sqrt(n))
    start = 0
    if B[0]==2:
        start=1
        for x in range((n-sqrtn+M)%2,2*M+1,2):
            CheckArray[x]+=1
            
    for p in B[start:]:
        l = p.bit_length()
        s= TonelliShanks(n,p)
        for x in range((s-sqrtn+M)%p, 2*M+1,p):
            CheckArray[x]+=l
        for x in range((-s-sqrtn+M)%p, 2*M+1,p):
            CheckArray[x]+=l
    Candidates = []
    for x in range(0,2*M+1):
        a = pow(x+sqrtn-M,2)-n
        if a.bit_length()<=CheckArray[x]:
            Candidates.append(x+sqrtn-M)
    return(Candidates)
    
    
#disclog(n,p) returns the least k so that p^k>n.  This is used to help decide how many 
def disclog(n,p):
        if n<=1:
            return(0)
        count = 0
        current=1
        while(current<n):
            current*=p
            count+=1
        return(count)
    


    
   
#Smooth Trial Division takes two inputs, n and B (a list of smooth prime factors to consider).  It checks if n factors completely over B.  If it does, it returns the vector true, then the vector describing the factorization.
# else it returns false, then as much factoring as it could muster 
def SmoothTrialDivision(n,B):
    b=len(B)
    Factorization = [0]*(b+1)
    if n<0:
        Factorization[-1] = 1
        n*=-1
    left_to_factor = n

    if n==0:
        return([True,Factorization])
    for i in range(b):
        p=B[i]
        while(left_to_factor%p ==0):
            left_to_factor//=p
            Factorization[i]+=1
    if left_to_factor ==1:
        return([True,Factorization])
    else:
        return([False,Factorization])