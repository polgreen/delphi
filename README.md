# Delphi

Delphi is a prototype implementation of SyMO and SMTO (see https://www2.eecs.berkeley.edu/Pubs/TechRpts/2021/EECS-2021-10.html)

### Building

- update the gitsubmodule (CBMC)
~~~
git submodule init
git submodule update
~~~
- ensure you have the dependencies for CBMC installed (Flex and Bison, and GNU make) (see https://github.com/diffblue/cbmc/blob/develop/COMPILING.md)
- download and patch minisat, and compile cbmc:
~~~
cd lib/cbmc/src
make minisat2-download
make
~~~
- compile delphi
~~~
cd delphi/src
make
~~~
