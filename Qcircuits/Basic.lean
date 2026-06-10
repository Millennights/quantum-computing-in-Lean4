import Mathlib

open Matrix Complex

noncomputable section

namespace DiracRepr

/-! ## Basic Vectors (Kets and Bras) -/

/-- Ket |0⟩ = (1, 0)ᵀ -/
def ket0 : Matrix (Fin 2) (Fin 1) ℂ := !![1; 0]

/-- Ket |1⟩ = (0, 1)ᵀ -/
def ket1 : Matrix (Fin 2) (Fin 1) ℂ := !![0; 1]

/-- Bra ⟨0| = (1, 0) — the conjugate transpose of |0⟩ -/
def bra0 : Matrix (Fin 1) (Fin 2) ℂ := !![1, 0]

/-- Bra ⟨1| = (0, 1) — the conjugate transpose of |1⟩ -/
def bra1 : Matrix (Fin 1) (Fin 2) ℂ := !![0, 1]


/-! ## Basic Matrices B₀, B₁, B₂, B₃-/

/-- B₀ = |0⟩⟨0| -/
def B0 : Matrix (Fin 2) (Fin 2) ℂ := ket0 * bra0

/-- B₁ = |0⟩⟨1| -/
def B1 : Matrix (Fin 2) (Fin 2) ℂ := ket0 * bra1

/-- B₂ = |1⟩⟨0| -/
def B2 : Matrix (Fin 2) (Fin 2) ℂ := ket1 * bra0

/-- B₃ = |1⟩⟨1| -/
def B3 : Matrix (Fin 2) (Fin 2) ℂ := ket1 * bra1


/-! ## Scalar constant: 1/√2 -/

/-- The scalar 1/√2 -/
abbrev s2 : ℂ := ↑(Real.sqrt 2 / 2)


/-! ## Derived states: |+⟩ and |−⟩ -/

/-- |+⟩ = (1/√2)|0⟩ + (1/√2)|1⟩ -/
def ket_plus : Matrix (Fin 2) (Fin 1) ℂ := s2 • ket0 + s2 • ket1

/-- |−⟩ = (1/√2)|0⟩ − (1/√2)|1⟩ -/
def ket_minus : Matrix (Fin 2) (Fin 1) ℂ := s2 • ket0 + (-s2) • ket1


/-! ## Quantum Gates -/

/-- 2×2 Identity matrix -/
def I₂ : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- Pauli-X gate (bit flip): X = |0⟩⟨1| + |1⟩⟨0| = B₁ + B₂ -/
def X_gate : Matrix (Fin 2) (Fin 2) ℂ := B1 + B2

/-- Pauli-Y gate: Y = -i·|0⟩⟨1| + i·|1⟩⟨0| -/
-- I = 0 + 1i
def Y_gate : Matrix (Fin 2) (Fin 2) ℂ := (-I) • B1 + I • B2

/-- Pauli-Z gate (phase flip): Z = |0⟩⟨0| − |1⟩⟨1| = B₀ − B₃ -/
def Z_gate : Matrix (Fin 2) (Fin 2) ℂ := B0 - B3

/-- Hadamard gate: H = (1/√2)(B₀ + B₁ + B₂ − B₃) -/
def H_gate : Matrix (Fin 2) (Fin 2) ℂ :=
  s2 • B0 + s2 • B1 + s2 • B2 + (-s2) • B3


/-! ## Tensor Product (Kronecker Product)
We define the Kronecker product for matrices indexed by `Fin`,
using `Fin.divNat` and `Fin.modNat` to map indices.
-/
/-- Kronecker (tensor) product of two matrices.
    For `A : Matrix (Fin m) (Fin n) ℂ`
    and `B : Matrix (Fin p) (Fin q) ℂ`,
    `kron A B : Matrix (Fin (m*p)) (Fin (n*q)) ℂ`. -/
def kron {m n p q : ℕ}
  (A : Matrix (Fin m) (Fin n) ℂ)
  (B : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin (m * p)) (Fin (n * q)) ℂ :=
  Matrix.of fun i j => A i.divNat j.divNat * B i.modNat j.modNat
infixl:70 " ⊗ " => kron


/-! ### Measurement operators -/

/-- Measurement operator M₀ = B₀ = |0⟩⟨0| (projector onto |0⟩) -/
def M0_meas : Matrix (Fin 2) (Fin 2) ℂ := B0

/-- Measurement operator M₁ = B₃ = |1⟩⟨1| (projector onto |1⟩) -/
def M1_meas : Matrix (Fin 2) (Fin 2) ℂ := B3


/-! ## Multi-qubit Gates -/

/-- Controlled-NOT (CNOT) gate: CX = B₀ ⊗ I₂ + B₃ ⊗ X -/
def CX : Matrix (Fin 4) (Fin 4) ℂ := B0 ⊗ I₂ + B3 ⊗ X_gate


/-! ## Simp lemmas for matrix element access -/
@[simp] lemma ket0_apply : ket0 = !![1; 0] := rfl
@[simp] lemma ket1_apply : ket1 = !![0; 1] := rfl
@[simp] lemma bra0_apply : bra0 = !![1, 0] := rfl
@[simp] lemma bra1_apply : bra1 = !![0, 1] := rfl

end DiracRepr
end
