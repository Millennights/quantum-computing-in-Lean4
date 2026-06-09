import Qcircuits.Basic

open Matrix Complex

noncomputable section

namespace DiracRepr

/-! ## Additional Quantum Gates
These gates are used in the
QFT,
Deutsch-Jozsa,
Simon,
Superdense coding protocols.
-/

/-! ### Phase gate S (π/2 phase) -/

/-- S gate = |0⟩⟨0| + i|1⟩⟨1| = B₀ + i·B₃ -/
def S_gate : Matrix (Fin 2) (Fin 2) ℂ := B0 + I • B3

/-! ### T gate (π/4 phase) -/

/-- T gate = |0⟩⟨0| + e^(iπ/4)|1⟩⟨1|
    e^(iπ/4) = (1+i)/√2 -/
def T_gate : Matrix (Fin 2) (Fin 2) ℂ :=
  B0 + ((1 + I) / Complex.ofReal (Real.sqrt 2)) • B3

/-- PT is the phase gate used in QFT.v. In the Coq code it is T_gate. -/
abbrev PT : Matrix (Fin 2) (Fin 2) ℂ := T_gate

/-! ### Controlled-S gate (CS) -/

/-- Controlled-S gate: CS = B₀ ⊗ I₂ + B₃ ⊗ S -/
def CS : Matrix (Fin 4) (Fin 4) ℂ := B0 ⊗ I₂ + B3 ⊗ S_gate

/-! ### Reverse CNOT gate (XC) -/

/-- XC = reverse CNOT: target is qubit 1, control is qubit 2.
    XC = I₂ ⊗ B₀ + X ⊗ B₃ -/
def XC : Matrix (Fin 4) (Fin 4) ℂ := I₂ ⊗ B0 + X_gate ⊗ B3

/-! ### Controlled-I⊗T gate (CIT) for 3-qubit QFT -/

/-- CIT = B₀ ⊗ I₂ ⊗ I₂ + B₃ ⊗ I₂ ⊗ PT
    Used in the 3-qubit QFT circuit -/
def CIT : Matrix (Fin 8) (Fin 8) ℂ := B0 ⊗ I₂ ⊗ I₂ + B3 ⊗ I₂ ⊗ PT

/-! ### Controlled-I⊗X gate (CIX) for Simon's algorithm -/

/-- CIX = B₀ ⊗ I₂ ⊗ I₂ + B₃ ⊗ I₂ ⊗ X
    Used in Simon's algorithm (s=11 case) -/
def CIX : Matrix (Fin 8) (Fin 8) ℂ := B0 ⊗ I₂ ⊗ I₂ + B3 ⊗ I₂ ⊗ X_gate

/-! ### Multi-qubit states -/

/-- |0000⟩ for 4-qubit circuits -/
def ket0000 : Matrix (Fin 16) (Fin 1) ℂ := ket0 ⊗ (ket0 ⊗ (ket0 ⊗ ket0))

/-- |0001⟩ -/
def ket0001 : Matrix (Fin 16) (Fin 1) ℂ := ket0 ⊗ (ket0 ⊗ (ket0 ⊗ ket1))

/-- |0010⟩ -/
def ket0010 : Matrix (Fin 16) (Fin 1) ℂ := ket0 ⊗ (ket0 ⊗ (ket1 ⊗ ket0))

/-- |0011⟩ -/
def ket0011 : Matrix (Fin 16) (Fin 1) ℂ := ket0 ⊗ (ket0 ⊗ (ket1 ⊗ ket1))

/-- |0100⟩ -/
def ket0100 : Matrix (Fin 16) (Fin 1) ℂ := ket0 ⊗ (ket1 ⊗ (ket0 ⊗ ket0))

/-- |0101⟩ -/
def ket0101 : Matrix (Fin 16) (Fin 1) ℂ := ket0 ⊗ (ket1 ⊗ (ket0 ⊗ ket1))

/-- |0110⟩ -/
def ket0110 : Matrix (Fin 16) (Fin 1) ℂ := ket0 ⊗ (ket1 ⊗ (ket1 ⊗ ket0))

/-- |0111⟩ -/
def ket0111 : Matrix (Fin 16) (Fin 1) ℂ := ket0 ⊗ (ket1 ⊗ (ket1 ⊗ ket1))

/-- |1000⟩ -/
def ket1000 : Matrix (Fin 16) (Fin 1) ℂ := ket1 ⊗ (ket0 ⊗ (ket0 ⊗ ket0))

/-- |1001⟩ -/
def ket1001 : Matrix (Fin 16) (Fin 1) ℂ := ket1 ⊗ (ket0 ⊗ (ket0 ⊗ ket1))

/-- |1010⟩ -/
def ket1010 : Matrix (Fin 16) (Fin 1) ℂ := ket1 ⊗ (ket0 ⊗ (ket1 ⊗ ket0))

/-- |1011⟩ -/
def ket1011 : Matrix (Fin 16) (Fin 1) ℂ := ket1 ⊗ (ket0 ⊗ (ket1 ⊗ ket1))

/-- |1100⟩ -/
def ket1100 : Matrix (Fin 16) (Fin 1) ℂ := ket1 ⊗ (ket1 ⊗ (ket0 ⊗ ket0))

/-- |1101⟩ -/
def ket1101 : Matrix (Fin 16) (Fin 1) ℂ := ket1 ⊗ (ket1 ⊗ (ket0 ⊗ ket1))

/-- |1110⟩ -/
def ket1110 : Matrix (Fin 16) (Fin 1) ℂ := ket1 ⊗ (ket1 ⊗ (ket1 ⊗ ket0))

/-- |1111⟩ -/
def ket1111 : Matrix (Fin 16) (Fin 1) ℂ := ket1 ⊗ (ket1 ⊗ (ket1 ⊗ ket1))

/-! ### Gate actions on basis states -/

theorem S_gate_ket0 : S_gate * ket0 = ket0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [S_gate, B0, B3, ket0, Matrix.mul_apply, Fin.sum_univ_succ]

theorem S_gate_ket1 : S_gate * ket1 = I • ket1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [S_gate, B0, B3, ket1, Matrix.mul_apply, Fin.sum_univ_succ]

/-! ### CX action on |+⟩⊗|+⟩ and |+⟩⊗|-⟩ -/

/-
CX|+,+⟩ = |+,+⟩ (used in Deutsch-Jozsa)
-/
theorem CX_ketpp : CX * (ket_plus ⊗ ket_plus) = ket_plus ⊗ ket_plus := by
  unfold CX ket_plus; norm_num [ B0, B3, X_gate, B1, ket0, ket1, bra0, bra1, kron ] ;
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ Fin.sum_univ_succ, Matrix.mul_apply, B2 ] ;
  · simp +decide [ Fin.divNat, Fin.modNat, I₂ ] at *;
  · simp +decide [ Fin.divNat, Fin.modNat, I₂ ] at *;
  · simp +decide [ Fin.divNat, Fin.modNat ] at *;
  · simp +decide [ Fin.divNat, Fin.modNat ] at *

/-
CX|+,−⟩ = |−,−⟩ (phase kickback)
-/
theorem CX_ketpm : CX * (ket_plus ⊗ ket_minus) = ket_minus ⊗ ket_minus := by
  unfold CX ket_plus ket_minus;
  rw [ ← Matrix.ext_iff ];
  norm_num [ Fin.forall_fin_succ, Matrix.mul_apply ];
  simp +decide [ B0, B3, X_gate, kron ];
  simp +decide [ Fin.sum_univ_succ, Fin.divNat, Fin.modNat, I₂, B1, B2 ];
  rfl

end DiracRepr
end
