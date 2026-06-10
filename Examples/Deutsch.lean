import Qcircuits.ObsEquiv

open Matrix Complex

noncomputable section

namespace DiracRepr

/-! ## Additional definitions needed for Deutsch's algorithm -/

/-- not_CX gate: controlled-NOT with control on |0⟩ instead of |1⟩
    not_CX = B₀ ⊗ X + B₃ ⊗ I₂ -/
def not_CX : Matrix (Fin 4) (Fin 4) ℂ := B0 ⊗ X_gate + B3 ⊗ I₂


/-! ## Helpers: Kronecker products of kets (Fin 4 × Fin 1) -/

/-- |0⟩ ⊗ |1⟩ -/
abbrev ket01 : Matrix (Fin 4) (Fin 1) ℂ := ket0 ⊗ ket1

/-- |0⟩ ⊗ |−⟩ -/
abbrev ket0m : Matrix (Fin 4) (Fin 1) ℂ := ket0 ⊗ ket_minus

/-- |1⟩ ⊗ |−⟩ -/
abbrev ket1m : Matrix (Fin 4) (Fin 1) ℂ := ket1 ⊗ ket_minus

/-- |+⟩ ⊗ |−⟩ -/
abbrev ketpm : Matrix (Fin 4) (Fin 1) ℂ := ket_plus ⊗ ket_minus

/-- |−⟩ ⊗ |−⟩ -/
abbrev ketmm : Matrix (Fin 4) (Fin 1) ℂ := ket_minus ⊗ ket_minus


/-! ## f(0) = f(1) = 0 -/

/-
Step 1: (H ⊗ H) × (|0⟩ ⊗ |1⟩) = |+⟩ ⊗ |−⟩
-/
theorem deutsch0_step1 :
    (H_gate ⊗ H_gate) * ket01 = ketpm := by
      have h_expand : ∀ (A B : Matrix (Fin 2) (Fin 2) ℂ) (C D : Matrix (Fin 2) (Fin 1) ℂ), (A ⊗ B) * (C ⊗ D) = (A * C) ⊗ (B * D) := by
        exact fun A B C D => L13_kron_mul_kron A B C D
      rw [ h_expand, H_ket0, H_ket1 ]

/-
Step 2: (I₂ ⊗ I₂) × (|+⟩ ⊗ |−⟩) = |+⟩ ⊗ |−⟩ 相位回扣
-/
theorem deutsch0_step2 :
    (I₂ ⊗ I₂) * ketpm = ketpm := by
      -- By definition of the tensor product, we know that I₂ ⊗ I₂ is the identity matrix on the tensor product space.
      have h_id : I₂ ⊗ I₂ = 1 := by
        -- By definition of tensor product, we know that I₂ ⊗ I₂ = 1.
        apply L8_kron_one;
      aesop

/-
Step 3: (H ⊗ I₂) × (|+⟩ ⊗ |−⟩) = |0⟩ ⊗ |−⟩
-/
theorem deutsch0_step3 :
    (H_gate ⊗ I₂) * ketpm = ket0m := by
      rw [ L13_kron_mul_kron ];
      convert congr_arg ( fun x => x ⊗ ket_minus ) ( H_ket_plus ) using 1;
      -- Since I₂ is the identity matrix, multiplying by it does not change the matrix.
      simp [I₂]

/-
Deutsch f=0: full circuit produces |0⟩ ⊗ |−⟩
-/
theorem deutsch0 :
    (H_gate ⊗ I₂) * ((I₂ ⊗ I₂) * ((H_gate ⊗ H_gate) * ket01)) = ket0m := by
      rw [deutsch0_step1];
      rw [deutsch0_step2, deutsch0_step3]

/-
Density matrix version
-/
theorem Ddeutsch0 :
    super ((H_gate ⊗ I₂) * ((I₂ ⊗ I₂) * (H_gate ⊗ H_gate))) (density ket01) =
    density ket0m := by
      rw [ ← deutsch0 ];
      simp [super, density];
      simp +decide only [Matrix.mul_assoc]


/-! ## f(0) = f(1) = 1 -/

/-
Step 2: (I₂ ⊗ X) × (|+⟩ ⊗ |−⟩) = (-1) • (|+⟩ ⊗ |−⟩) f=1,对y取反
-/
theorem deutsch1_step2 :
    (I₂ ⊗ X_gate) * ketpm = (-1 : ℂ) • ketpm := by
      simp +decide [← Matrix.ext_iff, Fin.forall_fin_succ, Matrix.mul_apply];
      simp +decide [Fin.sum_univ_succ, DiracRepr.kron];
      simp +decide [ Fin.divNat, Fin.modNat, X_gate, ket_plus, ket_minus ] ; ring_nf ; norm_num [ Complex.ext_iff ] ;
      norm_num [ sq, I₂, B1, B2 ] at *

/-
Deutsch f=1
-/
theorem deutsch1 :
    (H_gate ⊗ I₂) * ((I₂ ⊗ X_gate) * ((H_gate ⊗ H_gate) * ket01)) =
    (-1 : ℂ) • ket0m := by
      convert congr_arg ( fun x => ( H_gate ⊗ I₂ ) * x ) ( deutsch1_step2 ) using 1;
      · rw [ ← deutsch0_step1 ];
      · rw [ Matrix.mul_smul ];
        rw [ ← deutsch0_step3 ]

/-
Observational equivalence version
-/
theorem Odeutsch1 :
    obs_equiv
    ((H_gate ⊗ I₂) * ((I₂ ⊗ X_gate) * ((H_gate ⊗ H_gate) * ket01)))
    ket0m := by
    rw[deutsch1]
    apply obs_equiv_symm
    exact ⟨ -1, by norm_num, by norm_num ⟩


/-! ## f(0) = 0, f(1) = 1 -/

/-
Step 2: CX × (|+⟩ ⊗ |−⟩) = |−⟩ ⊗ |−⟩
-/
theorem deutsch2_step2 :
    CX * ketpm = ketmm := by
      unfold CX ketpm;
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [ B0, B3, X_gate, ket_plus, ket_minus, ketmm, Matrix.mul_apply ] ;
      · simp +decide [kron];
        simp +decide [ Fin.sum_univ_succ, Fin.divNat, Fin.modNat, I₂, B1, B2 ];
      · simp +decide [Fin.sum_univ_succ, B1, B2, I₂];
        simp +decide [kron];
        simp +decide [ Fin.divNat, Fin.modNat ];
      · simp +decide [Fin.sum_univ_succ, kron];
        simp +decide [ Fin.divNat, Fin.modNat, B1, B2, I₂ ];
      · simp +decide [kron];
        simp +decide [ Fin.sum_univ_succ, Fin.divNat, Fin.modNat, I₂, B1, B2 ]

/-
(H ⊗ I₂) × (|−⟩ ⊗ |−⟩) = |1⟩ ⊗ |−⟩
-/
theorem deutsch2_step3 :
    (H_gate ⊗ I₂) * ketmm = ket1m := by
      rw [ show ketmm = ket_minus ⊗ ket_minus from rfl, show ket1m = ket1 ⊗ ket_minus from rfl, ← H_ket_minus ];
      rw [ L13_kron_mul_kron ];
      norm_num [ Matrix.mul_apply, I₂ ]

/-
Deutsch f=CX
-/
theorem deutsch2 :
    (H_gate ⊗ I₂) * (CX * ((H_gate ⊗ H_gate) * ket01)) = ket1m := by
      grind +suggestions


/-! ## f(0) = 1, f(1) = 0 -/

/-
Step 2: not_CX × (|+⟩ ⊗ |−⟩) = (-1) • (|−⟩ ⊗ |−⟩)
-/
theorem deutsch3_step2 :
    not_CX * ketpm = (-1 : ℂ) • ketmm := by
      simp [not_CX, B0, B3, I₂];
      simp +decide [ ← Matrix.ext_iff, Fin.forall_fin_succ, X_gate, ketpm, ketmm ];
      simp +decide [Matrix.mul_apply, B1, B2, ket_plus, ket_minus];
      simp +decide [Fin.sum_univ_succ, Matrix.one_apply, Matrix.of_apply, kron];
      simp +decide [ Fin.divNat, Fin.modNat ] at *

/-
Deutsch f=not_CX
-/
theorem deutsch3 :
    (H_gate ⊗ I₂) * (not_CX * ((H_gate ⊗ H_gate) * ket01)) =
    (-1 : ℂ) • ket1m := by
      convert congr_arg ( fun x => ( H_gate ⊗ I₂ ) * x ) ( deutsch3_step2 ) using 1;
      · exact congrArg _ ( congrArg _ ( by exact deutsch0_step1 ) );
      · simp +decide [ketmm];rw[L13_kron_mul_kron];rw[I₂,L8_one_mul,H_ket_minus,ket1m];


/-
Observational equivalence version
-/
theorem Odeutsch3 :
    obs_equiv
    ((H_gate ⊗ I₂) * (not_CX * ((H_gate ⊗ H_gate) * ket01)))
    ket1m := by
      use (-1 : ℂ);
      convert deutsch3 using 1;
      norm_num [ neg_eq_iff_eq_neg ]
      exact neg_eq_iff_eq_neg

end DiracRepr
end
