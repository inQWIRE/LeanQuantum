# Quantumlib.lean

A formal verification library for quantum computing in Lean 4, loosely inspired by [QuantumLib](https://github.com/inQWIRE/QuantumLib).

## Overview

Quantumlib.lean is a formalization of quantum computing concepts in Lean 4, built on top of Mathlib. It provides:

- **Quantum Gates**: Hadamard, Pauli gates (X, Y, Z), rotation gates, phase shifts, controlled gates (CNOT), and more
- **Pauli Operators**: Efficient representation of n-qubit Pauli operators with phase tracking and custom notation
- **Pauli Maps**: Linear combinations of Pauli operators for quantum error correction
- **Stabilizer Codes**: Formalization of quantum error correcting codes (bit flip code, Shor's 9-qubit code)
- **Quantum States**: Bra/Ket notation and quantum basis states
- **Matrix Operations**: Kronecker products, tensor powers, unitary verification
- **Proof Automation**: Custom tactics for quantum gate equality proofs

This library aims to provide a rigorous foundation for reasoning about quantum circuits, quantum error correction, and quantum algorithms.

## Features

### Quantum Gates

The library implements standard quantum gates with full formalization:

- **Single-qubit gates**:
  - `hadamard`: Hadamard gate (H)
  - `sqrtx`: Square root of X gate (√X or V gate)
  - `σx`, `σy`, `σz`: Pauli matrices
  - `phaseShift φ`: Phase shift gate S(φ)
  - `xRotate θ`, `yRotate θ`: Rotation gates Rx(θ), Ry(θ)
  - `rotate θ φ δ`: General single-qubit rotation U3(θ, φ, δ)

- **Multi-qubit gates**:
  - `cnot`: Controlled-NOT gate
  - `swap`: SWAP gate
  - `controlM M`: Controlled version of any gate M
  - `hadamardK k`: k-fold tensor product of Hadamard gates

### Pauli Operators and Notation

Efficient representation of multi-qubit Pauli operators with decidable equality:

```lean
@[ext]
structure Pauli (n : ℕ) where
  m : ZMod 4        -- Phase: (-i)^m
  z : BitVec n      -- Z components
  x : BitVec n      -- X components
deriving DecidableEq, BEq, Fintype
```

**Custom notation** using `[P| ... ]` syntax:

```lean
-- Single Pauli operators
[P| XXI ]   -- X ⊗ X ⊗ I (3-qubit operator)
[P| ZZI ]   -- Z ⊗ Z ⊗ I
[P| iXYZ ]  -- i·(X ⊗ Y ⊗ Z) with phase
[P| -XYZ ]  -- -(X ⊗ Y ⊗ Z) negative phase

-- Pauli multiplication (automatic phase tracking)
[P| XXI ] * [P| IYZ ]  -- Computes product with correct phase
```

The notation automatically:
- Computes tensor products from string notation
- Tracks phases (including ±1, ±i)
- Handles Y = iXZ decomposition
- Pretty-prints back to readable form

Features:
- **Decidable equality** for fast comparison
- **Efficient multiplication** using phase tracking via `phaseFlipsWith`
- **Commutator checking**: `P.commutesWith Q`
- **Weight calculation**: number of non-identity Paulis
- **Kronecker product** (tensor): `P ⊗ Q`
- **Conversion to complex matrices**: `P.toCMatrix`

### Pauli Maps

Linear combinations of Pauli operators using `[PA| ... ]` notation:

```lean
-- Single Pauli as a map
[PA| XXI ]

-- Linear combination with coefficients
[PA| #(2) • XXI + #(3) • ZZI ]

-- Multiplication (automatically normalized)
[PA| (XXI + ZZI) * IYZ ]
```

`PauliMap n` is defined as `MonoidAlgebra ℂ (Pauli n)`, representing expressions like:
```
∑ᵢ cᵢ Pᵢ
```
where `cᵢ ∈ ℂ` and `Pᵢ` are Pauli operators.

Operations:
- **Normalized form**: Automatically extracts phases into coefficients
- **Addition and multiplication**: Full ring structure
- **Conversion to matrices**: `pm.toCMatrix`

### Quantum Error Correction

**Stabilizer codes** (`Quantumlib/Data/Error/Operator.lean`):

```lean
structure StabilizerCode (n k : ℕ) where
  generators : List (Pauli n)      -- Stabilizer generators
  logicalX : Fin k → Pauli n        -- Logical X operators
  logicalZ : Fin k → Pauli n        -- Logical Z operators
  stabilizers_commute : ...         -- All stabilizers commute
  logical_commute : ...             -- Logical ops have correct commutation
  logical_independent : ...         -- Logical ops are independent of stabilizers
```

**Implemented codes**:

1. **3-qubit Bit Flip Code**:
```lean
def BitFlip.code : StabilizerCode 3 1
-- Generators: [P| ZZI ], [P| IZZ ]
-- Logical X: [P| XXX ]
-- Logical Z: [P| ZZZ ]
```

Proven properties:
- Corrects single-qubit X errors: `{[P| IIX ], [P| IXI ], [P| XII ]}`
- Syndrome calculation is injective on error set
- Stabilizer group membership is decidable

2. **Shor's 9-qubit Code**:
```lean
def Shor9.code : StabilizerCode 9 1
-- 8 generators (6 Z-type, 2 X-type)
-- Corrects arbitrary single-qubit errors
```

### Quantum States and Notation

Dirac notation for quantum states:

```lean
-- Computational basis states
∣0⟩  -- |0⟩ state
∣1⟩  -- |1⟩ state

-- Bra-ket products
∣0⟩⟨0∣  -- Projector onto |0⟩
∣0⟩⟨1∣  -- Outer product
⟨0∣1⟩  -- Inner product (equals 0)
```

### Proof Automation

Custom tactics for quantum computing proofs:

- **`solve_matrix`**: Automatically prove matrix equalities by case analysis on indices
  ```lean
  lemma hadamard_mul_hadamard : hadamard * hadamard = 1 := by
    solve_matrix [hadamard]
  ```

- **Future: `decide_complex`** (planned): Decision procedure for complex number equality in quantum gates, supporting ℚ[i], ℚ[√2, i], cyclotomic extensions, and trigonometric values

## Project Structure

```
Quantumlib/
├── Data/
│   ├── Basis/           # Quantum basis states and ket-bra notation
│   │   ├── Basic.lean       # Ket/bra definitions
│   │   ├── Notation.lean    # Dirac notation (∣0⟩, ∣1⟩, etc.)
│   │   └── Equivs.lean      # Basis equivalences and identities
│   ├── Gate/            # Quantum gates
│   │   ├── Basic.lean       # Core gates (Hadamard, CNOT, SWAP, √X)
│   │   ├── Pauli/           # Pauli operators
│   │   │   ├── Defs.lean       # Pauli structure and operations
│   │   │   ├── Lemmas.lean     # Pauli algebra lemmas
│   │   │   └── Notation.lean   # [P| ... ] and [PA| ... ] notation
│   │   ├── Rotate.lean      # Rotation gates (Rx, Ry, Rz, U3)
│   │   ├── PhaseShift.lean  # Phase shift gates (S, T)
│   │   ├── Equivs.lean      # Gate equivalences and identities
│   │   ├── Hermitian.lean   # Hermiticity proofs
│   │   ├── Unitary.lean     # Unitarity proofs
│   │   ├── ConjTranspose.lean
│   │   └── Lemmas.lean
│   └── Error/
│       └── Operator.lean    # Stabilizer codes and error correction
├── ForMathlib/          # Extensions to Mathlib (may be upstreamed)
│   └── Data/
│       ├── Complex/         # Complex number utilities
│       ├── Matrix/          # Matrix operations
│       │   ├── Basic.lean      # Matrix utilities
│       │   ├── Kron.lean       # Kronecker products
│       │   ├── Unitary.lean    # Unitary matrices
│       │   └── PowBitVec.lean  # Tensor powers (M^⊗k)
│       ├── BitVec/          # Bit vector utilities
│       │   ├── Basic.lean      # BitVec operations
│       │   └── Lemmas.lean     # BitVec lemmas
│       └── Fin.lean         # Finite type utilities
├── Tactic/              # Custom tactics
│   ├── SolveMatrix.lean # Matrix equality automation
│   └── Basic.lean
├── Computation.lean     # Quantum circuit computation examples
└── Basic.lean           # Main imports

```

## Installation

### Prerequisites

- [Lean 4](https://leanprover.github.io/) (v4.26.0-rc2 or compatible)
- [Lake](https://github.com/leanprover/lake) (Lean's build system)

### Building the Library

```bash
# Clone the repository
git clone https://github.com/inQWIRE/LeanQuantum
cd LeanQuantum

# Build the library
lake build
```

### Using in Your Project

Add to your `lakefile.lean`:

```lean
require quantumlib from git
  "https://github.com/inQWIRE/LeanQuantum"
```

Then import in your Lean files:

```lean
import Quantumlib
```

## Usage Examples

### Basic Gate Operations

```lean
import Quantumlib

-- Hadamard is its own inverse
example : hadamard * hadamard = 1 := by
  solve_matrix [hadamard]

-- Pauli X is a NOT gate
example : σx * ∣0⟩ = ∣1⟩ := by
  solve_matrix [σx]

-- Pauli gates square to identity
example : σx * σx = 1 := by
  solve_matrix [σx]
```

### Square Root of X Gate

```lean
-- √X exists and satisfies √X · √X = X
lemma sqrtx_mul_sqrtx : sqrtx * sqrtx = σx := by
  simp [sqrtx, σx]
  ring_nf
  norm_num [Complex.I_sq]
```

### Pauli Operators with Notation

```lean
import Quantumlib.Data.Gate.Pauli

-- Create Pauli operators using notation
#check [P| XXI ]   -- Pauli 3
#check [P| ZZZ ]   -- Pauli 3
#check [P| iXYZ ]  -- Pauli 3 (with phase i)

-- Multiplication automatically tracks phases
example : [P| X ] * [P| Y ] = [P| iZ ] := by
  decide

-- Commutation checking
example : [P| XX ].commutesWith [P| ZZ ] = true := by
  decide

example : [P| XZ ].commutesWith [P| ZX ] = false := by
  decide
```

### Pauli Maps (Linear Combinations)

```lean
import Quantumlib.Data.Gate.Pauli

-- Single Pauli operator as a map
#check [PA| XXI ]

-- Linear combinations
def myObservable : PauliMap 3 := [PA| #(2) • XXI + #(3) • ZZI ]

-- Products (automatically normalized)
example : [PA| X ] * [PA| Y ] = [PA| #(Complex.I) • Z ] := by
  rfl
```

### Quantum Error Correction

```lean
import Quantumlib.Data.Error.Operator

-- The 3-qubit bit flip code
example : BitFlip.code.generators = [[P| ZZI ], [P| IZZ ]] := by
  rfl

-- Syndrome of an error
example : BitFlip.code.syndrome [P| IIX ] = [false, true] := by
  rfl

-- The code corrects single X errors
example : BitFlip.code.corrects {[P| IIX ], [P| IXI ], [P| XII ]} :=
  BitFlip.corrects_single_qubit_errors
```

### Multi-qubit Gates

```lean
-- CNOT acts as controlled-X
lemma cnot_decompose : cnot = ∣1⟩⟨1∣ ⊗ σx + ∣0⟩⟨0∣ ⊗ 1 := by
  solve_matrix [cnot, σx]
```

## Verified Properties

The library includes formal proofs of key quantum computing properties:

- **Gate identities**: H² = I, X² = I, Y² = I, Z² = I
- **Hermiticity**: Pauli gates, Hadamard, rotation gates are Hermitian
- **Unitarity**: All gates preserve inner products
- **Pauli commutation**: [X,Y] = 2iZ, etc.
- **Gate decompositions**: CNOT, controlled gates, √X
- **Stabilizer properties**: Generators commute, logical operators anticommute
- **Error correction**: Bit flip code corrects single-qubit X errors

## Development Roadmap

### Current Status ✅

- [x] Basic quantum gates (H, X, Y, Z, CNOT, SWAP, √X)
- [x] Pauli operator algebra with decidable equality
- [x] Custom Pauli notation `[P| ... ]` and `[PA| ... ]`
- [x] PauliMap for linear combinations
- [x] Stabilizer code framework
- [x] 3-qubit bit flip code (fully verified)
- [x] Shor's 9-qubit code (partial verification)
- [x] Ket-bra notation
- [x] Rotation and phase shift gates
- [x] `solve_matrix` tactic for gate equality proofs
- [x] Hermiticity verification

### In Progress 🚧

- [ ] **Robust `solve_matrix` via decidable complex equality**: Building a decision procedure for complex number equality in the algebraic fragment used by quantum gates (ℚ[i], ℚ[√2, i], cyclotomic extensions, trigonometric values)

### Planned Features 📋

- [ ] Complete unitarity proofs for rotation gates
- [ ] More quantum error correction codes
  - [ ] 5-qubit perfect code
  - [ ] 7-qubit Steane code
  - [ ] Surface codes
  - [ ] CSS codes
- [ ] Quantum circuits
  - [ ] Circuit composition
  - [ ] Circuit optimization
  - [ ] Circuit equivalence
- [ ] Quantum algorithms
  - [ ] Deutsch-Jozsa
  - [ ] Grover's algorithm
  - [ ] Quantum Fourier Transform
  - [ ] Shor's algorithm (circuit)
- [ ] Measurement and observables
- [ ] Density matrices and mixed states
- [ ] Quantum channels and noise

## Contributing

Contributions are welcome! Areas where help is particularly appreciated:

1. **Completing unitarity proofs** for rotation gates
2. **More stabilizer codes** (Steane, surface codes, etc.)
3. **Quantum algorithms** formalization
4. **Documentation and examples**
5. **Performance improvements** to tactics

Please open an issue or pull request on [GitHub](https://github.com/inQWIRE/LeanQuantum).

## Related Work

- **[Lean-QuantumInfo](https://github.com/Timeroot/Lean-QuantumInfo)**: Another (more complete) quantum computing library in Lean 4
- **[QuantumLib](https://github.com/inQWIRE/QuantumLib)**: Quantum computing library in Coq (inspiration for this project)
- **[Mathlib](https://github.com/leanprover-community/mathlib4)**: Lean 4's mathematics library
- **[SQIR](https://github.com/inQWIRE/SQIR)**: Small Quantum Intermediate Representation in Coq
- **[Qiskit](https://qiskit.org/)**: IBM's quantum computing framework (Python)

## Citation

If you use Quantumlib.lean in your research, please cite:

```bibtex
@software{quantumlib_lean,
  title = {Quantumlib.lean: Formal Verification of Quantum Computing in Lean 4},
  author = {Fady Adal},
  year = {2025},
  url = {https://github.com/inQWIRE/LeanQuantum}
}
```

## Acknowledgments

This project is loosely inspired by [QuantumLib](https://github.com/inQWIRE/QuantumLib) from the inQWIRE group.

Special thanks to:
- The Lean community for Lean 4 and Mathlib
- Professor Robert Rand and the inQWIRE group

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

---

**Author**: Fady Adal
**Status**: Active development
**Lean Version**: v4.26.0-rc2
**Repository**: https://github.com/inQWIRE/LeanQuantum
