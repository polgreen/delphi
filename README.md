# Delphi

Delphi is a prototype implementation of SyMO and SMTO (see https://www2.eecs.berkeley.edu/Pubs/TechRpts/2021/EECS-2021-10.html). Example benchmarks can be found here: https://github.com/polgreen/oracles

### Building
Prerequisites: All prerequisties for CBMC must be installed (https://github.com/diffblue/cbmc/blob/develop/COMPILING.md). Plus Z3 and CVC4(version 1.8 or greater) must be added to $PATH.  
- Z3 downloads:https://github.com/Z3Prover/z3/releases
- CVC4 downloads: https://github.com/cvc5/cvc5/releases

update the gitsubmodule (CBMC)
~~~
git submodule init
git submodule update
~~~
Ensure you have the dependencies for CBMC installed (Flex and Bison, and GNU make) (see https://github.com/diffblue/cbmc/blob/develop/COMPILING.md). Then 
download and patch minisat, and compile cbmc as follows:
~~~
cd lib/cbmc/src
make minisat2-download
make
~~~
Compile delphi
~~~
cd delphi/src
make
~~~

The binary is found at `delphi/src/delphi/delphi`. 

To run delphi on a file:
~~~
delphi file.smt2
~~~
To run delphi on a synthesis file:
~~~
delphi file.sl
~~~
To run delphi in interactive mode use command `delphi --smto` or 'delphi --symo`

### Input format

Delphi accepts an extension of the SyGuS-IF language. The following declares an oracle function symbol of name `NAME`, associated to an oracle `binaryname` with type IntxInt->Bool. You do not need to declare the oracle separately, this one declaration is sufficient: 
~~~
(declare-oracle-fun NAME binaryname ((x Int)(y Int)) Bool)
~~~
The following declares an oracle `binaryname` that accepts two input integers, and returns a single boolean. These values are substituted into the expression `(= (f x y) z)` to generate a synthesis constraint:
~~~
(oracle-constraint binaryname ((x Int)(y Int))((z Bool))
 (= (f x y) z) )
~~~

Input files must have the file extension '.smt' if the problem is an SMTO problem and '.sl' if the problem is a synthesis problem. 

### Examples
#### SMTO
The following SMTO example checks whether there exist 3 prime factors fo 76:
~~~
(declare-oracle-fun isPrime isprime ((x Int)) Bool)
(declare-fun f1 () Int)
(declare-fun f2 () Int)
(declare-fun f3 () Int)
(assert (and (isPrime f1)(isPrime f2)(isPrime f3)))
(assert (= (* f1 f2 f3) 76))
(check-sat) 
~~~
The oracle for isprime can be found here: https://github.com/polgreen/oracles/tree/master/prime_oracle

#### SyMO
The following SyMo example uses two oracles to synthesise a function that performs a pixel by pixel transformation on an image.  
~~~
(synth-fun tweak ((pixel (_ BitVec 8))) (_ BitVec 8))
; correctness (verification)
(declare-oracle-fun pixel_correct ./pixel_oracle_brighter.sh ((-> (_ BitVec 8) (_ BitVec 8))) Bool)

(constraint (pixel_correct tweak))

; hints (synthesis)
(oracle-constraint
  ./pixel_oracle_brighter.sh
  ((tweak (-> (_ BitVec 8) (_ BitVec 8))))
  ((correct Bool) (pixelIn (_ BitVec 8)) (pixelOut (_ BitVec 8)))
  (=> (not correct) (= (tweak pixelIn) pixelOut)))
(check-synth)
~~~
The oracles for the image transformations can be found here: https://github.com/polgreen/oracles/tree/master/image_oracles

