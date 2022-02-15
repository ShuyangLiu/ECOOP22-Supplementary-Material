# #14: Compiling Volatile Correctly in Java 
Paper submission number: 14

## Overview
The following components are included in the VM:
- The extended Herd7 implementation with Java architecture
  - **Location**: `~/herd`
  - Ocaml source code
  - Requires Ocaml 4.09.0 and dune 2.9.1 (already installed in the VM)
  - For build instructions, please see the [Getting Started](#getting-started) section.

- Litmus Tests that appeared in our paper (benchmark)
  - **Location**: `~/litmus`
  - We provide two types of litmus tests:
    - Tests written in Java: `~/litmus/java/litmus`
    - Tests written in Power: `~/litmus/ppc`
  - The JAM21 model can be found at `~/litmus/java/jam21.cat`
  - The JAM19 model can be found at `~/litmus/java/jam19.cat`
  - Can be executed using the extended Herd7 tool with the JAM model 
  - For running instructions, please see the [Getting Started](#getting-started) section.

- Coq proofs for some of the theorems in the paper (proof)
  - **Location**: `~/coq`
  - Coq proofs 
  - Requires Coq 8.06.1 with Ocaml 4.02.3 (already installed in the VM)
  - For build instructions, please see the [Getting Started](#getting-started) section.

## Artifact Requirements
* Oracle VM VirtualBox >= 6.1

## Getting Started

### Step 1: Starting the Virtual Machine
To start the virtural machine, import the OVA file to virtual box and click 'Start'
* **Username**: `user1`
* **Password**: `password`

The virtual machine runs Ubuntu 20.04 with bash as the default shell. All required dependencies should already be installed. 

### Step 2: Building Herd7
* Change to the directory of herd7:
  ```bash
  cd ~/herd
  ```
* Make sure the Ocaml version is correct:
  ```bash
  opam switch 4.09.0
  ```
* Refresh environment variables:
  ```bash
  eval $(opam env)
  ```
* Build the source code (please ignore the warnings):
  ```
  make 
  ```
* There should be an executable file at `~/herd/_build/default/herd/herd.exe`

### Step 3: Running Litmus Tests
* Make sure the executable is built before this step (see step 2)
* To execute a litmus test (with file name `<testfile>`) using the JAM model:
  ```bash
  ~/herd/_build/default/herd/herd.exe -I ~/herd/herd/libdir \
                                      -model ~/litmus/java/jam21.cat \
                                      <testfile>
  ```
  For example, to run the `~/litmus/java/litmus/volatile-non-sc.4.litmus`:
  ```bash
  /herd/_build/default/herd/herd.exe -I ~/herd/herd/libdir \
                                      -model ~/litmus/java/jam21.cat \
                              ~/litmus/java/litmus/volatile-non-sc.4.litmus
  ```
* To execute a litmus test with other memory models, simply change the `-model` option to the model's `cat` file. If the model is included by default (such as the PowerPC model), then the option can be omitted. For example, to run litmus tests written in Power instructions such as `~/litmus/ppc/volatile-non-sc.4.ppc.litmus` with the Power memory model:
  ```bash
  /herd/_build/default/herd/herd.exe -I ~/herd/herd/libdir \
                                      ~/litmus/ppc/volatile-non-sc.4.ppc.litmus
  ```
  Note that the JAM model is not included by default. Therefore it should always be explicitly specified using the `-model` option.

* There are three types of results: `Never`, `Sometimes`, and `Always`. It can be found at the line starting with `Observation...` in the output of herd. For example, the test `volatile-non-sc.5.ppc.litmus` is allowed by the the Power memory model, so the output looks like:
  ```
  ...
  Observation volatile-non-sc.5.ppc Sometimes 1 94
  ...
  ```
  The results should match with our results claimed in the paper.

* You can also run all the litmus tests using the python script we included `~/run.py`. The script runs both JAM19 and JAM21 on the litmus tests provided inside `~/litmus/java/litmus` . To run the script:
  ```bash
  python3 ~/run.py
  ```
  An output file `~/results.md` includes a table comparing the results running JAM19 and JAM21 on the litmus tests. 

### Step 4: Writing Custom Java Litmus Test
New litmus tests written in Java syntax can be created using the following format. First, specify `Java` on the first line so that the tool will choose the Java architecture:
```
Java <testname>
```
`<testname>` is where the name of the test is. 

Then specify the initial condition in brackets. For example, if we have two threads (thread 0 and thread 1) accessing memory location `x` and `y`, which are initialized to `0`:
```
{
  x = 0; y = 0;
  0:X=x; 0:Y=y;
  1:X=x; 1:Y=y;
}
```

The program body can be specified after the initialization. For example, if we wish thread 0 to write to `y` with a value of `1` in `Volatile` mode and then read from `x` in `Volatile` mode:
```
Thread0 {
  Y.setVolatile(1);
  int r1 = X.getVolatile();
}
```
For the full supported grammar, please see the grammar file at `~/herd/lib/JavaParser.mly`

Finally, specify the condition to be checked by the tool using the memory model. For example, the following says "there exists an execution such that at the end the `r1` variable on thread 0 is 0 and the `r2` variable on thread 1 is 0":
```
exists
(0:r1=0 /\ 1:r2=0)
```
Save it to a file `<testname>.litmus` and use the commands from the previous section to run it. Note that Java litmus tests can only be executed with `jam21.cat` or `jam19.cat` since they use a specific set of memory actions that are different from other languages. 


### Step 5: Compiling the Coq proofs
  * Switch to Coq 8.06.1 with Ocaml 4.02.3:
    ```bash
    opam switch 4.02.3
    ```
  * Refresh the envionment variables:
    ```bash
    eval $(opam env)
    ```
  * Change directory:
    ```bash
    cd ~/coq
    ```
  * Generate Makefile:
    ```bash
    coq_makefile -f _CoqProject -o Makefile
    ```
  * Build:
    ```bash
    make clean all
    ```
## Troubleshooting
* `Command `coqc` not found` even after switching to 4.02.3
  - Usually this is due to the environment variables not updated. please make sure to run `eval $(opam env)` every time switching ocaml version. 

* `bash:~/herd/_build/default/herd/herd.exe: No such file for directory`
  - Please make sure `herd7` is built before running the litmus tests as they are not installed 

## Badges
We would like to claim the "functional", "reusable", and "available" badges for this artifact. 

* What are claims about the artifact’s functionality to be evaluated by the committee?
  1. Our extended herd7 with Java supports the Java VarHandle syntax for litmus test with the following methods from the API:
      - Read Operations: `get()`, `getOpaque()`, `getAcquire()`, `getVolatile()`
      - Write Operations: `set()`, `setOpaque()`, `setRelease()`, `setVolatile()`
      - Fences: `fullFence()`, `acquireFence()`, `releaseFence()`
      - Read-modify-write Operations: `getAndAdd()`, `getAndAnd()`, `getAndOr()`, `getAndXor()`, `getAndAddAcquire()`, `getAndAndAcquire()`, `getAndOrAcquire()`, `getAndXorAcquire()`, `getAndAddRelease()`, `getAndAndRelease()`, `getAndOrRelease()`, `getAndXorRelease()`
  2. The Coq proofs are sound (automatically checked by the compiler)

* Which activities described in the paper have led to the creation of the artifact components?
  - To accuratly validate the revised JAM model we described in the paper, the herd7 tool extended with the Java "architecture" is essential. The current official herd7 tool suite (https://github.com/herd/herdtools7) does not support litmus tests written in Java
  - The Coq proofs ensure the soundness of our proofs in Appendix H of the paper.

* Which data or conclusions from the paper are generated/supported by the artifact components?
  - The results of running the litmus tests with our implementation of Herd is reproducable and the test results are the same as claimed in Appendix K (Fig. 18, 19, 23) of the paper.

* What are the authors' claims about the artifact's reusability to be evaluated by the committee?
  - Custom litmus tests using the Java VarHandle API can be created following instructions from Step 4 and executed following Step 3 in the Getting Started section.
  - The grammar of the litmus tests can be extended by modifying `JavaParser.mly` and `JavaLexer.mll`
  - The litmus tests in Java syntax can be easily converted to the test format for jcstress test suite for stress tests

* For the available badge, we agree to publish our work under a Creative Commons license. While we are certain about the Coq proofs and the litmus tests, we realize the situation for our extended Herd7 tool might be different and complicated since [Herd7](https://github.com/herd/herdtools7) is a open source software under a CeCILL-B license hosted on GitHub. If the option of publishing it under a Creative Commons license is not available to us, we are going to create a pull request and ask the maintainers of Herd7 to merge our extension to the official repository. We have already contacted the author of Herd7 and they are willing to do so once we update the tool to their current version.
