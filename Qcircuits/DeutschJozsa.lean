import Qcircuits.NQubit

open Matrix Complex

noncomputable section

namespace DiracRepr


/-! ## Function Properties -/

/-- A Boolean function f : Fin (2^n) → Bool is **constant** if it maps
    all inputs to the same value. -/
def IsConstant {n : ℕ} (f : Fin (2 ^ n) → Bool) : Prop :=
  (∀ x, f x = true) ∨ (∀ x, f x = false)

/-- A Boolean function f : Fin (2^n) → Bool is **balanced** if exactly
    half the inputs map to true and half to false. -/
def IsBalanced {n : ℕ} (f : Fin (2 ^ n) → Bool) : Prop :=
  (Finset.univ.filter (fun x => f x = true)).card = 2 ^ (n - 1)

/-- Constant and balanced are mutually exclusive when n ≥ 1. -/
theorem constant_not_balanced {n : ℕ} (hn : n ≥ 1) (f : Fin (2 ^ n) → Bool)
    (hc : IsConstant f) : ¬IsBalanced f := by
  cases hc <;> simp_all +decide [IsBalanced]
  · omega
  · positivity


/-! ## Deutsch-Jozsa Phase Sum -/

/-- The Deutsch-Jozsa phase sum: ∑_x (-1)^{f(x)} ∈ ℤ. -/
def djPhaseSum (n : ℕ) (f : Fin (2 ^ n) → Bool) : ℤ :=
  ∑ x : Fin (2 ^ n), if f x then -1 else 1

theorem djPhaseSum_eq_sub_twice_card (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    djPhaseSum n f = (2 ^ n : ℤ) -
      2 * ((Finset.univ.filter (fun x => f x = true)).card : ℤ) := by
  unfold djPhaseSum
  simp +decide [Finset.sum_ite, Finset.filter_not]
  have := Finset.card_add_card_compl (Finset.filter (fun x => f x = true) Finset.univ)
  norm_num at *; linarith

theorem djPhaseSum_const_false {n : ℕ} (f : Fin (2 ^ n) → Bool) (h : ∀ x, f x = false) :
    djPhaseSum n f = (2 ^ n : ℤ) := by
  unfold djPhaseSum; aesop

theorem djPhaseSum_const_true {n : ℕ} (f : Fin (2 ^ n) → Bool) (h : ∀ x, f x = true) :
    djPhaseSum n f = -(2 ^ n : ℤ) := by
  unfold djPhaseSum; aesop

/-- Phase sum for constant functions equals ±2^n -/
theorem djPhaseSum_constant {n : ℕ} (f : Fin (2 ^ n) → Bool) (hc : IsConstant f) :
    djPhaseSum n f = (2 ^ n : ℤ) ∨ djPhaseSum n f = -(2 ^ n : ℤ) := by
  rcases hc with h | h
  · exact Or.inr (djPhaseSum_const_true f h)
  · exact Or.inl (djPhaseSum_const_false f h)

/-- Phase sum for balanced functions is zero -/
theorem djPhaseSum_balanced {n : ℕ} (hn : n ≥ 1) (f : Fin (2 ^ n) → Bool)
    (hb : IsBalanced f) :
    djPhaseSum n f = 0 := by
  rw [djPhaseSum_eq_sub_twice_card, hb]
  cases n <;> simp_all +decide [pow_succ']

theorem djPhasesum_correctness {n : ℕ} (hn : n ≥ 1) (f : Fin (2 ^ n) → Bool)
    (promise : IsConstant f ∨ IsBalanced f) :
    IsConstant f ↔ djPhaseSum n f ≠ 0 := by
  constructor <;> intro hf <;> cases' promise with h_const h_balanced
  · cases djPhaseSum_constant f h_const <;> aesop
  · exact absurd (constant_not_balanced hn f hf) (by tauto)
  · assumption
  · exact False.elim <| hf <| djPhaseSum_balanced hn f h_balanced


/-! ## General Oracle Matrix -/

/-- General quantum oracle U_f for f : Fin (2^n) → Bool.
    U_f = ∑_x |x⟩⟨x| ⊗ (if f(x) then X_gate else I₂)
    This implements |x⟩|y⟩ ↦ |x⟩|y ⊕ f(x)⟩. -/
def Uf_general (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    Matrix (Fin (2 ^ n * 2)) (Fin (2 ^ n * 2)) ℂ :=
  ∑ x : Fin (2 ^ n), stdProj x ⊗ (if f x then X_gate else I₂)


/-! ## Phase Kickback -/

/-- X gate sends |−⟩ to −|−⟩ -/
theorem X_ket_minus' : X_gate * ket_minus = -ket_minus := by
  unfold ket_minus
  simp +decide [X_ket0, X_ket1, DiracRepr.X_gate]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, B1, B2]


/-! ## DJ Circuit with General Oracle -/

/-- (H^⊗n ⊗ H) |0⟩^⊗n|1⟩ = |+⟩^⊗n |−⟩ -/
theorem DJ_step1 (n : ℕ) :
    (H_n n ⊗ H_gate) * (ket0_n n ⊗ ket1) = ketp_n n ⊗ ket_minus := by
  rw [L13_kron_mul_kron, QFT_ket0_n, H_ket1]

/-- The DJ circuit output for the general oracle -/
def DJ_output (n : ℕ) (f : Fin (2 ^ n) → Bool) : Matrix (Fin (2 ^ n * 2)) (Fin 1) ℂ :=
  (H_n n ⊗ H_gate) * (Uf_general n f * ((H_n n ⊗ H_gate) * (ket0_n n ⊗ ket1)))


/-! ### Balanced Case
For balanced f, we show the output is orthogonal to |0⟩^n in the first register,
by connecting the circuit amplitude to the phase sum. -/

/-- Entry-wise characterization of U_f -/
theorem Uf_general_apply (n : ℕ) (f : Fin (2 ^ n) → Bool)
    (i j : Fin (2 ^ n * 2)) :
    Uf_general n f i j =
      if i.divNat = j.divNat then
        (if f i.divNat then X_gate else I₂) i.modNat j.modNat
      else 0 := by
  unfold Uf_general; simp +decide [ Finset.sum_apply, Matrix.sum_apply ] ;
  rw [ Finset.sum_eq_single ( i.divNat ) ];
  · split_ifs <;> simp_all +decide [ stdProj_apply, kron ];
    · tauto;
    · aesop;
  · intro b _ hb; rw [ show ( stdProj b ⊗ if f b = true then X_gate else I₂ ) i j = ( stdProj b ) ( i.divNat ) ( j.divNat ) * ( if f b = true then X_gate else I₂ ) ( i.modNat ) ( j.modNat ) by rfl ] ; rw [ stdProj_apply ] ; aesop;
  · aesop

/-- The phase-kicked state after oracle, before second Hadamard.
    Defined entry-wise: the x-th amplitude is (-1)^{f(x)} · s2^n -/
def phaseVec (n : ℕ) (f : Fin (2 ^ n) → Bool) : Matrix (Fin (2 ^ n)) (Fin 1) ℂ :=
  Matrix.of fun i _ => (if f i then (-1 : ℂ) else 1) * s2 ^ n

/-- Oracle action: U_f(|+⟩^n ⊗ |−⟩) = phaseVec ⊗ |−⟩ -/
theorem oracle_on_ketp_minus (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    Uf_general n f * (ketp_n n ⊗ ket_minus) = phaseVec n f ⊗ ket_minus := by
  ext i j; simp +decide [ *, Matrix.mul_apply, Matrix.of_apply ] ;
  simp +decide [ Uf_general_apply, phaseVec, Matrix.mul_apply ];
  simp +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, ketp_n_entry, ket_minus, X_gate, I₂ ];
  erw [ show ( Finset.filter ( fun x => i.divNat = x.divNat ) Finset.univ : Finset ( Fin ( 2 ^ n * 2 ) ) ) = { ⟨ i.divNat * 2, by linarith [ Fin.is_lt i.divNat, Fin.is_lt i ] ⟩, ⟨ i.divNat * 2 + 1, by linarith [ Fin.is_lt i.divNat, Fin.is_lt i ] ⟩ } from ?_ ] ; simp +decide [ Finset.sum_pair, Finset.sum_singleton, Matrix.mul_apply, Matrix.of_apply, Finset.sum_ite ] ; ring;
  · rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp +decide [ Fin.modNat, h ];
    · split_ifs <;> simp +decide [ *, Matrix.mul_apply, Matrix.of_apply, Finset.sum_ite ];
      · simp +decide [ B1, B2, Matrix.mul_apply, Matrix.of_apply, Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, ketp_n_entry, ket_minus, X_gate, I₂, kron ];
        simp +decide [ *, Fin.add_def, Fin.mul_def, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ];
        simp +decide [ Fin.divNat, Fin.modNat, Nat.add_div, Nat.mul_div_assoc, Nat.mul_mod, Nat.add_mod, h ];
        rw [ ketp_n_entry ] ; ring;
        norm_num [ s2 ] ; ring;
      · simp +decide [ *, Matrix.mul_apply, Matrix.of_apply, Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, Fin.modNat, Fin.divNat, kron, Matrix.kroneckerMap ] ; ring!;
        simp +decide [ *, ketp_n_entry, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
        norm_num [ show f ⟨ i / 2, by linarith [ Fin.is_lt i, Nat.div_mul_le_self i 2, Nat.mod_add_div i 2 ] ⟩ = false from by simpa using ‹¬f i.divNat = true› ] ; ring;
        norm_num;
    · split_ifs <;> simp +decide [ *, Matrix.mul_apply, Matrix.of_apply, Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, B1, B2, I₂, ketp_n_entry, ket_minus, X_gate, I₂ ] ; ring;
      · simp +decide [ *, Matrix.mul_apply, Matrix.of_apply, Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', B1, B2, I₂, ketp_n, phaseVec, kron ] ; ring;
        simp +decide [ Fin.divNat, Fin.modNat, h, ketp_n_entry ] ; ring;
        norm_num [ mul_assoc, ← mul_pow ];
      · simp +decide [ *, Matrix.mul_apply, Matrix.of_apply, Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, B1, B2, I₂, ketp_n_entry, ket_minus, X_gate, I₂, kron ] ; ring;
        simp +decide [ Fin.modNat, Fin.divNat, h, ketp_n_entry ] ; ring;
        norm_num;
  · ext ⟨ x, hx ⟩ ; simp +decide [ Fin.ext_iff, Nat.div_eq_of_lt ] ;
    lia

/-- Inner product: (ketp_n)ᴴ * phaseVec = (1/2^n) · djPhaseSum · I -/
theorem ketp_conj_phaseVec (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    (ketp_n n)ᴴ * phaseVec n f =
    (1 / (2 : ℂ) ^ n) • ((djPhaseSum n f : ℤ) : ℂ) •
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j; simp +decide [ Matrix.mul_apply, djPhaseSum ] ; ring;
  simp +decide [ Fin.eq_zero, phaseVec, ketp_n_entry_conj, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
  rw [ Fin.eq_zero i, Fin.eq_zero j ] ; norm_num [ ketp_n_entry ] ; ring;
  norm_cast ; norm_num [ pow_mul', ← mul_pow ]

/-- Inner product of ⟨0|^n⟨1| with the DJ output connects to the phase sum -/
theorem DJ_amplitude_zero (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    (bra0_n n ⊗ bra1) * DJ_output n f =
    (1 / (2 : ℂ) ^ n) • ((djPhaseSum n f : ℤ) : ℂ) •
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  -- Unfold DJ_output and rewrite using DJ_step1.
  have h1 : DJ_output n f = (H_n n ⊗ H_gate) * ((Uf_general n f) * (ketp_n n ⊗ ket_minus)) := by
    rw [ DJ_output, DJ_step1 ];
  rw [ h1, oracle_on_ketp_minus ];
  rw [ L13_kron_mul_kron, L13_kron_mul_kron ];
  rw [ ← Matrix.mul_assoc, bra0_n_mul_H_n, ketp_conj_phaseVec ] ; norm_num [ H_ket_minus ];
  ext i j; simp +decide [ Matrix.mul_apply ] ;
  fin_cases i ; fin_cases j ; norm_num [ Matrix.smul_eq_diagonal_mul ];
  exact mul_one _


/-! ### Balanced  -/

/-- For balanced f with n ≥ 1, the DJ output is orthogonal to |0⟩^n ⊗ |1⟩ -/
theorem DJ_general_balanced_orthogonal {n : ℕ} (hn : n ≥ 1)
    (f : Fin (2 ^ n) → Bool) (hb : IsBalanced f) :
    (bra0_n n ⊗ bra1) * DJ_output n f = 0 := by
  rw [DJ_amplitude_zero]
  have h := djPhaseSum_balanced hn f hb
  simp [h]


/-! ### Constant  -/

theorem DJ_circuit_correctness {n : ℕ} (hn : n ≥ 1) (f : Fin (2 ^ n) → Bool)
    (promise : IsConstant f ∨ IsBalanced f) :
    IsConstant f ↔
      ((bra0_n n ⊗ bra1) * DJ_output n f ≠ 0) := by
  constructor
  · intro hc
    rw [DJ_amplitude_zero]
    have h_ps := djPhaseSum_constant f hc
    simp only [ne_eq, smul_eq_zero, one_div]
    cases h_ps <;> simp_all +decide [ pow_eq_zero_iff' ]
  · intro h_nonzero
    by_contra h_not_const
    have h_bal : IsBalanced f := by tauto
    exact h_nonzero (DJ_general_balanced_orthogonal hn f h_bal)


theorem DJ_circuit_correctness_1 {n : ℕ} (hn : n ≥ 1) (f : Fin (2 ^ n) → Bool)
    (promise : IsConstant f ∨ IsBalanced f) :
    IsConstant f ↔
      (((bra0_n n ⊗ bra1) * DJ_output n f)^2 = 1) := by
      sorry


/-! ## example Constant f ≡ 0 -/

/-- Oracle for the constant function f ≡ 0: identity on all qubits.
    U_f|x⟩|y⟩ = |x⟩|y ⊕ 0⟩ = |x⟩|y⟩. -/
def Uf_const0 (n : ℕ) : Matrix (Fin (2 ^ n * 2)) (Fin (2 ^ n * 2)) ℂ :=
  (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) ⊗ I₂

/-- The f≡0 oracle preserves |+⟩^n ⊗ |−⟩ -/
theorem DJ_const0_oracle (n : ℕ) :
    Uf_const0 n * (ketp_n n ⊗ ket_minus) = ketp_n n ⊗ ket_minus := by
  simp only [Uf_const0]
  rw [L13_kron_mul_kron, Matrix.one_mul, show I₂ * ket_minus = ket_minus from by simp [I₂]]

/-- Full DJ circuit for f ≡ 0: measurement yields |0⟩^n ⊗ |1⟩ -/
theorem DJ_full_const0 (n : ℕ) :
    (H_n n ⊗ H_gate) * (Uf_const0 n * ((H_n n ⊗ H_gate) * (ket0_n n ⊗ ket1)))
    = ket0_n n ⊗ ket1 := by
  rw [DJ_step1, DJ_const0_oracle, L13_kron_mul_kron, QFT_ketp_n, H_ket_minus]


/-! ## example Constant f ≡ 1 -/

/-- Oracle for the constant function f ≡ 1: applies X to ancilla.
    U_f|x⟩|y⟩ = |x⟩|y ⊕ 1⟩. -/
def Uf_const1 (n : ℕ) : Matrix (Fin (2 ^ n * 2)) (Fin (2 ^ n * 2)) ℂ :=
  (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) ⊗ X_gate

/-- The f≡1 oracle maps |+⟩^n ⊗ |−⟩ to −(|+⟩^n ⊗ |−⟩) -/
theorem DJ_const1_oracle (n : ℕ) :
    Uf_const1 n * (ketp_n n ⊗ ket_minus) = -(ketp_n n ⊗ ket_minus) := by
  simp only [Uf_const1]
  rw [L13_kron_mul_kron, Matrix.one_mul, X_ket_minus]
  ext i j
  simp [kron]

/-- Full DJ circuit for f ≡ 1: measurement yields −(|0⟩^n ⊗ |1⟩) -/
theorem DJ_full_const1 (n : ℕ) :
    (H_n n ⊗ H_gate) * (Uf_const1 n * ((H_n n ⊗ H_gate) * (ket0_n n ⊗ ket1)))
    = -(ket0_n n ⊗ ket1) := by
  rw [DJ_step1, DJ_const1_oracle]
  rw [Matrix.mul_neg, L13_kron_mul_kron, QFT_ketp_n, H_ket_minus]


/-! ## example Balanced Function: f(x) = x mod 2 (generalized identity) -/

/-- The generalized identity function: f(x) = (x mod 2 = 1).
    For n = 1, this equals f(0) = false, f(1) = true, i.e., f(x) = x. -/
def f_mod2 (n : ℕ) : Fin (2 ^ n) → Bool :=
  fun x => decide (x.val % 2 = 1)

/-- The identity function is balanced for n ≥ 1 -/
theorem f_mod2_balanced {n : ℕ} (hn : n ≥ 1) : IsBalanced (f_mod2 n) := by
  unfold IsBalanced f_mod2;
  rcases n with ( _ | n ) <;> simp_all +decide [ Nat.pow_succ' ];
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => ⟨ 2 * i + 1, by linarith [ pow_succ' 2 n ] ⟩;
  · simp +zetaDelta at *;
    exact fun a ha => ⟨ a / 2, Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt a, pow_succ' 2 n ], by congr; linarith [ Nat.mod_add_div a 2 ] ⟩;
  · norm_num [ Nat.add_mod ];
  · aesop

/-- For n = 1, f_mod2 agrees with the identity on Fin 2 -/
theorem f_mod2_n1 : f_mod2 1 = fun x : Fin 2 => decide (x = 1) := by
  decide +revert

/-- The DJ circuit correctly identifies f_mod2 as balanced for any n ≥ 1 -/
theorem DJ_f_mod2_balanced {n : ℕ} (hn : n ≥ 1) :
    (bra0_n n ⊗ bra1) * DJ_output n (f_mod2 n) = 0 :=
  DJ_general_balanced_orthogonal hn (f_mod2 n) (f_mod2_balanced hn)

end DiracRepr
end
