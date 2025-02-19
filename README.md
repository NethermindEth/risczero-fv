# RISC Zero RISC-V zk circuit formalisation in Lean

This Lean repository contains a model of RISC Zero's Zirgen eDSL and its target MLIR,
together with the verification of several proof of concept zk circuits.

This repository is closely tied to the [verification condition generator](https://github.com/NethermindEth/risczero-fv-extractor/),
which extracts circuits from Zirgen, generates weakest preconditions and gives us template Lean files
where we specify and prove behaviour of said circuits.

We invite you to read a more thorough overview in the blog post '[Towards formal verification of the first RISC-V zkVM](https://www.nethermind.io/blog/towards-formal-verification-of-the-first-risc-v-zkvm)'.

## Running the formalisation

### Installing Lean and building the project
The simplest way to install the particular version of Lean we use is to [download and install the most recent version](https://lean-lang.org/lean4/doc/quickstart.html) of Lean and Elan.
Once it is in place, simply run `lake build` in the root directory. This will download all the necessary components and build the project.

### Looking at the examples
In `Risc0/Gadgets`, there are several examples with specifications and proofs.

The examples that are fully complete are: 
- RISC-V instruction decoder, in `Risc0/Gadgets/ComputeDecode`.
- IsZero circuit / gadget, in `Risc0/Gadgets/IsZero`.
- OneHot2 circuit / gadget, in `Risc0/Gadgets/OneHot2`.

The `.../Proofs.lean` file in each of the folders contains both the specifications and their proofs.
We customarily state `constraints_of_witness` and `spec_of_constraints`.
The former says that the generated witness conforms to the constraints and the latter states that
the constraints imply that our desired behaviour of the circuit holds, whatever that behaviour may be.
