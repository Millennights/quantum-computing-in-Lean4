import Qcircuits.Equiv

open Matrix Complex DiracRepr

noncomputable section

namespace DiracRepr

/-! ### Definition of observational equivalence -/

/-- Two matrices are observationally equivalent if they differ by a global phase.
    A ≈ₒ B ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ c • A = B -/
def obs_equiv {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ c • A = B
/-! 50代表优先级 -/
scoped infix:50 " ≈ₒ " => obs_equiv


/-! ### Observational equivalence is an equivalence relation -/

/-- Observational equivalence is reflexive: A ≈ₒ A -/
theorem obs_equiv_refl {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    A ≈ₒ A := by
  exact ⟨1, by simp, by simp⟩

/-
Observational equivalence is symmetric: A ≈ₒ B → B ≈ₒ A
-/
theorem obs_equiv_symm {m n : ℕ} {A B : Matrix (Fin m) (Fin n) ℂ}
    (h : A ≈ₒ B) : B ≈ₒ A := by
  obtain ⟨ c, hc, hc' ⟩ := h;
  refine' ⟨ c⁻¹, _, _ ⟩;
  · aesop;
  · rw [ ← hc', smul_smul, inv_mul_cancel₀ ( by aesop_cat ), one_smul ]

/-
Observational equivalence is transitive: A ≈ₒ B → B ≈ₒ C → A ≈ₒ C
-/
theorem obs_equiv_trans {m n : ℕ} {A B C : Matrix (Fin m) (Fin n) ℂ}
    (h1 : A ≈ₒ B) (h2 : B ≈ₒ C) : A ≈ₒ C := by
  -- Given ⟨c₁, hc₁, h₁⟩ with c₁ • A = B and ⟨c₂, hc₂, h₂⟩ with c₂ • B = C. Use c₂ * c₁ as witness.
  obtain ⟨c₁, hc₁, h₁⟩ := h1
  obtain ⟨c₂, hc₂, h₂⟩ := h2
  use c₂ * c₁;
  -- By definition of scalar multiplication, we have (c₂ * c₁) • A = c₂ • (c₁ • A).
  have h_assoc : (c₂ * c₁) • A = c₂ • (c₁ • A) := by
    exact?;
  aesop

/-- Observational equivalence is an equivalence relation. -/
theorem obs_equiv_equivalence (m n : ℕ) :
    Equivalence (@obs_equiv m n) :=
  ⟨obs_equiv_refl, fun h => obs_equiv_symm h, fun h1 h2 => obs_equiv_trans h1 h2⟩


/-! ### Observational equivalence is compatible with multiplication -/

/-
Observational equivalence is compatible with matrix multiplication:
    A ≈ₒ C → B ≈ₒ D → A × B ≈ₒ C × D
-/
theorem obs_equiv_mul {m n p : ℕ}
    {A C : Matrix (Fin m) (Fin n) ℂ}
    {B D : Matrix (Fin n) (Fin p) ℂ}
    (h1 : A ≈ₒ C) (h2 : B ≈ₒ D) :
    (A * B) ≈ₒ (C * D) := by
  obtain ⟨ c₁, hc₁, h₁ ⟩ := h1; obtain ⟨ c₂, hc₂, h₂ ⟩ := h2; use c₁ * c₂; simp_all +decide [ mul_assoc, smul_smul ] ;
  simp +decide [ ← h₁, ← h₂, mul_assoc, smul_mul_assoc ];
  rw [ smul_smul, mul_comm ]


/-! ### Characterization for operators -/

/-
Forward direction: if A ≈ₒ B then A acts equivalently to B on all states.
-/
theorem ObsEquiv_operator_fwd {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : A ≈ₒ B) (ψ : Matrix (Fin n) (Fin 1) ℂ) :
    (A * ψ) ≈ₒ (B * ψ) := by
  cases' h with c hc;
  exact ⟨ c, hc.1, by rw [ ← hc.2, Matrix.smul_mul ] ⟩

/-
Backward direction: if A and B act equivalently on all states, then A ≈ₒ B.
    This is the non-trivial direction corresponding to `sta_equiv_by_Mmult` in Equival.v.
-/
theorem ObsEquiv_operator_bwd {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ ψ : Matrix (Fin n) (Fin 1) ℂ, (A * ψ) ≈ₒ (B * ψ)) :
    A ≈ₒ B := by
  -- By definition of observational equivalence, we need to show that there exists a complex number $c$ with $‖c‖ = 1$ such that $c • A = B$.
  have h_exists_c : ∀ j : Fin n, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i : Fin n, c * A i j = B i j := by
    intro j
    obtain ⟨c, hc⟩ := h (Matrix.of (fun i k => if i = j then 1 else 0));
    exact ⟨ c, hc.1, fun i => by simpa [ Matrix.mul_apply ] using congr_fun ( congr_fun hc.2 i ) 0 ⟩;
  choose c hc using h_exists_c;
  by_cases hA : ∃ i j, A i j ≠ 0 <;> simp_all +decide [ funext_iff, Matrix.mul_apply ];
  · obtain ⟨i₀, j₀, hA₀⟩ : ∃ i₀ j₀, A i₀ j₀ ≠ 0 ∧ ∀ j, A i₀ j = 0 ∨ c j = c j₀ := by
      obtain ⟨i₀, j₀, hA₀⟩ : ∃ i₀ j₀, A i₀ j₀ ≠ 0 := hA
      have h_eq : ∀ j, A i₀ j = 0 ∨ c j = c j₀ := by
        intro j
        by_contra h_contra
        push_neg at h_contra
        have h_eq : ∀ t : ℂ, ∃ d : ℂ, ‖d‖ = 1 ∧ ∀ i : Fin n, d * (A i j₀ + t * A i j) = B i j₀ + t * B i j := by
          intro t
          obtain ⟨d, hd⟩ := h (Matrix.of (fun i k => if k = ⟨0, by linarith⟩ then if i = j₀ then 1 else if i = j then t else 0 else 0));
          use d; simp_all +decide [ ← Matrix.ext_iff, Fin.forall_fin_succ ] ;
          simp_all +decide [ Matrix.mul_apply, Finset.sum_ite ];
          by_cases hj : j = j₀ <;> simp_all +decide [ mul_comm, Finset.card_filter ]
        generalize_proofs at *; (
        obtain ⟨ d₁, hd₁, hd₁' ⟩ := h_eq 0; obtain ⟨ d₂, hd₂, hd₂' ⟩ := h_eq 1; simp_all +decide [ ← hc _ |>.2 ] ;
        have h_eq : ∀ t : ℂ, ∃ d : ℂ, ‖d‖ = 1 ∧ d * (A i₀ j₀ + t * A i₀ j) = c j₀ * A i₀ j₀ + t * (c j * A i₀ j) := by
          exact fun t => by obtain ⟨ d, hd₁, hd₂ ⟩ := h_eq t; exact ⟨ d, hd₁, hd₂ i₀ ⟩ ;
        generalize_proofs at *; (
        obtain ⟨ d₃, hd₃, hd₃' ⟩ := h_eq ( -A i₀ j₀ / A i₀ j ) ; simp_all +decide [ mul_div_cancel₀ ] ;
        grind))
      use i₀, j₀, hA₀, h_eq;
    refine' ⟨ c j₀, hc j₀ |>.1, _ ⟩;
    ext i j; specialize hA₀; cases hA₀.2 j <;> simp_all +decide [ ← eq_comm ] ;
    contrapose! h; simp_all +decide [ obs_equiv ] ;
    use Matrix.of (fun k l => if k = j then 1 else if k = j₀ then 1 else 0);
    intro x hx; intro H; have := congr_fun ( congr_fun H i ) ⟨ 0, by linarith [ Fin.is_lt i, Fin.is_lt j, Fin.is_lt j₀ ] ⟩ ; simp_all +decide [ Matrix.mul_apply ] ;
    have := congr_fun ( congr_fun H i₀ ) ⟨ 0, by linarith [ Fin.is_lt i₀, Fin.is_lt j, Fin.is_lt j₀ ] ⟩ ; simp_all +decide [ Matrix.mul_apply ] ;
    simp_all +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq' ];
    grind
  · exact ⟨ 1, by norm_num, by ext i j; simp +decide [ ← hc j |>.2 i, hA ] ⟩

/-- Two operators are observationally equivalent iff they act equivalently on all states.
    A ≈ₒ B ↔ ∀ ψ, A × ψ ≈ₒ B × ψ -/
theorem ObsEquiv_operator {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    A ≈ₒ B ↔ (∀ ψ : Matrix (Fin n) (Fin 1) ℂ, (A * ψ) ≈ₒ (B * ψ)) :=
  ⟨ObsEquiv_operator_fwd A B, ObsEquiv_operator_bwd A B⟩


/-! ### Characterization for states -/

/-
Two states are observationally equivalent iff they produce the same density matrix.
    ψ ≈ₒ φ ↔ ψ × ψ† = φ × φ†
-/
theorem ObsEquiv_state {n : ℕ}
    (ψ ϕ : Matrix (Fin n) (Fin 1) ℂ) :
    ψ ≈ₒ ϕ ↔ density ψ = density ϕ := by
  constructor <;> intro h <;> simp_all +decide [ ← Matrix.ext_iff, Fin.forall_fin_two, Complex.ext_iff ];
  · cases' h with c hc;
    simp_all +decide [ ← hc.2, density ];
    norm_num [ Complex.normSq, Complex.norm_def ] at hc;
    grind;
  · by_cases hψ : ψ = 0 <;> by_cases hϕ : ϕ = 0 <;> simp_all +decide [ density ];
    · exact?;
    · contrapose! hϕ; ext i j; simp_all +decide [ Matrix.mul_apply ] ;
      fin_cases j ; specialize h i i ; norm_num [ Complex.ext_iff ] at * ; constructor <;> nlinarith! [ h ] ;
    · contrapose! hψ; ext i j; simp_all +decide [ Matrix.mul_apply, Complex.ext_iff ] ;
      have := h i i; fin_cases j; constructor <;> nlinarith!;
    · obtain ⟨i, hi⟩ : ∃ i : Fin n, ψ i 0 ≠ 0 := by
        exact not_forall.mp fun h' => hψ <| by ext i j; fin_cases j; aesop;
      obtain ⟨j, hj⟩ : ∃ j : Fin n, ϕ j 0 ≠ 0 := by
        exact not_forall.mp fun h => hϕ <| by ext i j; fin_cases j; aesop;
      set c := ϕ i 0 / ψ i 0 with hc_def
      have hc_norm : ‖c‖ = 1 := by
        have := h i i; simp_all +decide [ Finset.sum_range_succ', Matrix.mul_apply ] ;
        rw [ div_eq_iff ] <;> simp_all +decide [ Complex.normSq, Complex.norm_def ];
        exact ne_of_gt <| Real.sqrt_pos.mpr <| by specialize h i i; exact not_le.mp fun h' => hi <| by refine' Complex.ext _ _ <;> norm_num <;> nlinarith;
      have hc_eq : ∀ j : Fin n, ϕ j 0 = c * ψ j 0 := by
        intro j; specialize h i j; simp_all +decide [ Matrix.mul_apply, Complex.ext_iff ] ;
        simp_all +decide [ Complex.div_re, Complex.div_im ];
        by_cases hi : ψ i 0 = 0 <;> simp_all +decide [ Complex.normSq, Complex.norm_def ];
        ring
        grind
      exact ⟨c, hc_norm, by
        ext j k; fin_cases k; simp +decide [ hc_eq j ] ;⟩


/-! ### Examples of observational equivalence -/

/-
|0⟩ is not observationally equivalent to |1⟩.
-/
theorem ket0_not_obs_equiv_ket1 : ¬ (ket0 ≈ₒ ket1) := by
  -- Assume for contradiction that ket0 ≈ₒ ket1.
  by_contra h
  obtain ⟨c, hc, hcA⟩ : ∃ c : ℂ, ‖c‖ = 1 ∧ c • ket0 = ket1 := by
    exact h;
  simp_all +decide [ ← List.ofFn_inj, Complex.ext_iff ]

/-
A state is observationally equivalent to its negation (global phase -1).
-/
theorem neg_obs_equiv {n : ℕ} (ψ : Matrix (Fin n) (Fin 1) ℂ) :
    ψ ≈ₒ (-ψ) := by
  exact ⟨ -1, by norm_num, by norm_num ⟩

/-
i • ψ is observationally equivalent to ψ (global phase i).
-/
theorem I_smul_obs_equiv {n : ℕ} (ψ : Matrix (Fin n) (Fin 1) ℂ) :
    ψ ≈ₒ (Complex.I • ψ) := by
  exact ⟨ I, by norm_num ⟩


/-! ### Global phase has no effect on measurement -/

/-
Observationally equivalent states produce the same measurement probabilities.
    If ψ ≈ₒ ϕ, then ⟨ψ|M|ψ⟩ = ⟨ϕ|M|ϕ⟩ for any Hermitian observable M.
-/
theorem obs_equiv_same_expectation {n : ℕ}
    (ψ ϕ : Matrix (Fin n) (Fin 1) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ = M)
    (h : ψ ≈ₒ ϕ) :
    ψᴴ * M * ψ = ϕᴴ * M * ϕ := by
  obtain ⟨ c, hc, rfl ⟩ := h;
  simp +decide [ ← mul_assoc, ← Matrix.ext_iff ] at *;
  rw [ Complex.mul_conj, Complex.normSq_eq_norm_sq ] ; aesop

end DiracRepr
end
