import Qcircuits.BernsteinVazirani

open Matrix Complex

noncomputable section

namespace DiracRepr

/-!
We reuse `dotSign`, `bdot_BV`, `dotSign_mul` and `H_n_entry` from
`BernsteinVazirani.lean`
-/


/-! ## Bitwise XOR on `Fin (2^n)` -/

/-- Bitwise XOR of two elements of `Fin (2^n)`. -/
def finXor {n : ℕ} (i s : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨i.val ^^^ s.val, Nat.xor_lt_two_pow i.is_lt s.is_lt⟩

@[simp] theorem finXor_val {n : ℕ} (i s : Fin (2 ^ n)) :
    (finXor i s).val = i.val ^^^ s.val := rfl

theorem finXor_involutive {n : ℕ} (s : Fin (2 ^ n)) :
    Function.Involutive (fun i : Fin (2 ^ n) => finXor i s) := by
  intro i
  apply Fin.ext
  simp [finXor]

/-- The permutation of `Fin (2^n)` given by XOR-ing with `s`, as an `Equiv`. -/
def finXorEquiv {n : ℕ} (s : Fin (2 ^ n)) : Fin (2 ^ n) ≃ Fin (2 ^ n) :=
  (finXor_involutive s).toPerm

@[simp] theorem finXorEquiv_apply {n : ℕ} (s i : Fin (2 ^ n)) :
    finXorEquiv s i = finXor i s := rfl


/-! ## Commutativity of the dot-product sign -/

theorem bdot_BV_comm (a b : ℕ) : bdot_BV a b = bdot_BV b a := by
  induction' a using Nat.binaryRec with a ih generalizing b;
  · induction' b using Nat.binaryRec with b ih;
    · rfl;
    · unfold bdot_BV; aesop;
  · unfold bdot_BV;
    cases a <;> simp_all +decide [ Nat.bit ];
    · cases b <;> aesop;
    · cases b <;> simp_all +decide [ Nat.add_div ]

theorem dotSign_comm (a b : ℕ) : dotSign a b = dotSign b a := by
  unfold dotSign; rw [bdot_BV_comm]


/-! ## the finXOR permutation matrix -/

/-- The permutation matrix sending `|b⟩ ↦ |b ⊕ z⟩`. -/
def permMat {n : ℕ} (z : Fin (2 ^ n)) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.of fun a b => if a.val = b.val ^^^ z.val then 1 else 0

/-- `permMat z · |b⟩ = |b ⊕ z⟩`. -/
theorem permMat_stdKet {n : ℕ} (z b : Fin (2 ^ n)) :
    permMat z * stdKet b = stdKet (finXor b z) := by
  ext a j;
  simp +decide [permMat, stdKet, Matrix.mul_apply];
  simp +decide [ Fin.ext_iff, finXor ]


/-! ## The Simon oracle and circuit -/

/-- The Simon oracle `U_f = ∑_x |x⟩⟨x| ⊗ P_{f(x)}`, acting as
    `|x⟩|y⟩ ↦ |x⟩|y ⊕ f(x)⟩` on `2n` qubits. -/
def Uf_simon (n : ℕ) (f : Fin (2 ^ n) → Fin (2 ^ n)) :
    Matrix (Fin (2 ^ n * 2 ^ n)) (Fin (2 ^ n * 2 ^ n)) ℂ :=
  ∑ x : Fin (2 ^ n), stdProj x ⊗ permMat (f x)

/-- The Simon circuit output state. -/
def Simon_output (n : ℕ) (f : Fin (2 ^ n) → Fin (2 ^ n)) :
    Matrix (Fin (2 ^ n * 2 ^ n)) (Fin 1) ℂ :=
  (H_n n ⊗ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) *
    (Uf_simon n f *
      ((H_n n ⊗ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) * (ket0_n n ⊗ ket0_n n)))

/-- The post-measurement (un-normalised) amplitude vector on the second register
    when the first register is measured in state `|x⟩`:
    `(1/2^n) ∑_i (-1)^{i·x} |f(i)⟩`. -/
def simonVec (n : ℕ) (f : Fin (2 ^ n) → Fin (2 ^ n)) (x : Fin (2 ^ n)) :
    Matrix (Fin (2 ^ n)) (Fin 1) ℂ :=
  (1 / (2 : ℂ) ^ n) • ∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i)


/-! ## Uniform superposition as a sum of basis states -/

/-- `|+⟩^⊗n = s2^n • ∑_x |x⟩`. -/
theorem ketp_n_eq_sum (n : ℕ) :
    ketp_n n = (s2 : ℂ) ^ n • ∑ x : Fin (2 ^ n), stdKet x := by
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  rw [ketp_n_entry, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  have hsum : (∑ x : Fin (2 ^ n), stdKet x i 0) = 1 := by
    rw [Finset.sum_eq_single i]
    · simp [stdKet]
    · intro b _ hb
      simp only [stdKet, Matrix.of_apply]
      rw [if_neg (fun h => hb h.symm)]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hsum, mul_one]


/-! ## Circuit simplification -/

/-- First Hadamard layer: `(H^⊗n ⊗ I)|0⟩^⊗n|0⟩^⊗n = |+⟩^⊗n |0⟩^⊗n`. -/
theorem simon_step1 (n : ℕ) :
    (H_n n ⊗ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) * (ket0_n n ⊗ ket0_n n)
      = ketp_n n ⊗ ket0_n n := by
  convert congr_arg₂ ( fun x y => x ⊗ y ) ( QFT_ket0_n n ) ( Matrix.one_mul _ ) using 1;
  convert L13_kron_mul_kron _ _ _ _ using 1

/-
Oracle action on the uniform superposition:
    `U_f (|+⟩^⊗n |0⟩^⊗n) = s2^n • ∑_x |x⟩|f(x)⟩`.
-/
theorem simon_step2 (n : ℕ) (f : Fin (2 ^ n) → Fin (2 ^ n)) :
    Uf_simon n f * (ketp_n n ⊗ ket0_n n)
      = (s2 : ℂ) ^ n • ∑ x : Fin (2 ^ n), (stdKet x ⊗ stdKet (f x)) := by
  rw [ketp_n_eq_sum, ket0_n_eq_stdKet, ← L6_smul_kron_left, Matrix.mul_smul]
  congr 1
  unfold Uf_simon
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [L13_kron_mul_kron]
  congr 1
  · -- stdProj x * (∑ y, stdKet y) = stdKet x
    rw [Matrix.mul_sum, Finset.sum_congr rfl (fun y _ => stdProj_stdKet x y),
      Finset.sum_ite_eq]
    simp
  · -- permMat (f x) * stdKet 0 = stdKet (f x)
    rw [permMat_stdKet]
    congr 1
    apply Fin.ext
    simp [finXor]

/-- Second Hadamard layer applied to `s2^n • ∑_x |x⟩|f(x)⟩`. -/
theorem simon_step3 (n : ℕ) (f : Fin (2 ^ n) → Fin (2 ^ n)) :
    (H_n n ⊗ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) *
        ((s2 : ℂ) ^ n • ∑ x : Fin (2 ^ n), (stdKet x ⊗ stdKet (f x)))
      = (s2 : ℂ) ^ n • ∑ x : Fin (2 ^ n), ((H_n n * stdKet x) ⊗ stdKet (f x)) := by
  rw [ Matrix.mul_smul, Finset.smul_sum ];
  convert congr_arg _ ( Matrix.mul_sum _ _ _ ) using 2;
  rw [ Finset.smul_sum ] ; congr ; ext ;
  rw [ L13_kron_mul_kron ] ; norm_num

/-
Simon simplification.  The partial measurement amplitude at `|x⟩` in the
    first register equals `simonVec n f x = (1/2^n) ∑_i (-1)^{i·x} |f(i)⟩`.
-/
theorem Simon_simplify (n : ℕ) (f : Fin (2 ^ n) → Fin (2 ^ n)) (x : Fin (2 ^ n)) :
    (stdBra x ⊗ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) * Simon_output n f
      = (simonVec n f x).submatrix (finCongr (one_mul (2 ^ n))) id := by
  -- Unfold `Simon_output` and apply the three circuit steps to rewrite the state.
  suffices h_suff : (stdBra x ⊗ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) * Simon_output n f
      = (s2 : ℂ) ^ n • ∑ i : Fin (2 ^ n),
          ((stdBra x * (H_n n * stdKet i)) ⊗ stdKet (f i)) by
    convert h_suff using 1;
    ext ⟨ a, ha ⟩ j;
    simp +decide [Matrix.sum_apply, Matrix.smul_apply] ; ring;
    simp +decide [ Matrix.mul_apply, kron, simonVec, stdKet, stdBra, H_n_entry,
      dotSign_comm ];
    simp +decide [Matrix.sum_apply, Fin.modNat] ; ring;
    norm_num [ Fin.ext_iff, Nat.mod_eq_of_lt ( show a < 2 ^ n from by linarith ),
      mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    norm_cast ; norm_num [ ← mul_pow ];
  -- Apply the three circuit steps to rewrite the state.
  have h_state : Simon_output n f
      = (s2 : ℂ) ^ n • ∑ i : Fin (2 ^ n), ((H_n n * stdKet i) ⊗ stdKet (f i)) := by
    unfold Simon_output;
    rw [ simon_step1, simon_step2, simon_step3 ];
  norm_num [ h_state, L13_kron_mul_kron, Matrix.mul_smul, Matrix.mul_sum ]


/-! ## Period structure -/

/-- `f` has nonzero period `s`: `f` is invariant under XOR-ing the input with `s`. -/
def HasPeriod {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n)) (s : Fin (2 ^ n)) : Prop :=
  s ≠ 0 ∧ ∀ x, f x = f (finXor x s)

/-- `dotSign` and `finXor`: `(-1)^{(i⊕s)·x} = (-1)^{i·x} · (-1)^{s·x}`. -/
theorem dotSign_finXor {n : ℕ} (i s x : Fin (2 ^ n)) :
    dotSign (finXor i s).val x.val = dotSign i.val x.val * dotSign s.val x.val := by
  simp only [finXor_val]
  rw [dotSign_mul]

/-
Key cancellation.  If `f` has period `s` and `s · x = 1`, then the
    amplitude vector `∑_i (-1)^{i·x} |f(i)⟩` is zero.
-/
theorem simonVec_eq_zero {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n)) (s x : Fin (2 ^ n))
    (hper : HasPeriod f s) (hsx : bdot_BV s.val x.val = true) :
    simonVec n f x = 0 := by
  -- `s · x = 1` means the sign attached to `s` is `-1`.
  have hs_sign : dotSign s.val x.val = -1 := by
    simp [dotSign, hsx]
  -- Reindex `i ↦ i ⊕ s`: using the period `f (i⊕s) = f i` and
  -- `(-1)^{(i⊕s)·x} = (-1)^{i·x}·(-1) `, the sum equals minus itself.
  have h_simp : ∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i)
      = ∑ i : Fin (2 ^ n), (-1 : ℂ) • dotSign i.val x.val • stdKet (f i) := by
    rw [← Equiv.sum_comp (finXorEquiv s)
        (fun i => dotSign i.val x.val • stdKet (f i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [finXorEquiv_apply]
    rw [dotSign_finXor, hs_sign, ← hper.2 i, smul_smul]
    congr 1
    ring
  -- Hence the sum is zero (it equals minus itself, in a torsion-free module).
  have h_zero_sum : ∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i) = 0 := by
    have h2 : (∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i))
        = -(∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i)) := by
      nth_rewrite 1 [h_simp]
      simp
    have h3 : (2 : ℂ) • (∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i)) = 0 := by
      rw [two_smul]; nth_rewrite 1 [h2]; abel
    have h4 := congrArg (fun M => (2 : ℂ)⁻¹ • M) h3
    simp only [smul_smul, smul_zero] at h4
    norm_num at h4
    exact h4
  unfold simonVec
  rw [h_zero_sum, smul_zero]


/-! ## Correctness_s ≠ 0 -/

/-- The full Simon promise: nonzero period `s`, `f` is `s`-periodic, and `f` is
    exactly two-to-one (its only collisions are `x` and `x ⊕ s`). -/
def SimonPromise {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n)) (s : Fin (2 ^ n)) : Prop :=
  s ≠ 0 ∧ (∀ x, f x = f (finXor x s)) ∧ (∀ x y, f x = f y → x = y ∨ y = finXor x s)

/-- `SimonPromise` entails the weaker `HasPeriod`. -/
theorem SimonPromise.hasPeriod {n : ℕ} {f : Fin (2 ^ n) → Fin (2 ^ n)} {s : Fin (2 ^ n)}
    (h : SimonPromise f s) : HasPeriod f s :=
  ⟨h.1, h.2.1⟩

/-- For `s ≠ 0` in `Fin (2^n)` we must have `1 ≤ n`. -/
theorem one_le_of_ne_zero {n : ℕ} (s : Fin (2 ^ n)) (hs : s ≠ 0) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · exfalso; apply hs; subst h; apply Fin.ext
    have := s.is_lt; simp only [pow_zero] at this; simp
  · exact h

/-- XOR-ing with a nonzero string never fixes a point. -/
theorem finXor_ne_self {n : ℕ} (i s : Fin (2 ^ n)) (hs : s ≠ 0) : finXor i s ≠ i := by
  intro h
  apply hs
  apply Fin.ext
  have hv : i.val ^^^ s.val = i.val := by
    have := congrArg Fin.val h; simpa [finXor] using this
  have h2 := congrArg (· ^^^ i.val) hv
  simp only [Nat.xor_comm, Nat.xor_self] at h2
  simpa [Nat.xor_comm] using h2

/-- Inner sum: for fixed `i`, summing the Gram weights over `k` gives `2`. -/
theorem simon_inner_sum {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n)) (s x : Fin (2 ^ n))
    (hpro : SimonPromise f s) (hsx : bdot_BV s.val x.val = false) (i : Fin (2 ^ n)) :
    ∑ k : Fin (2 ^ n),
        (if f i = f k then dotSign i.val x.val * dotSign k.val x.val else 0) = 2 := by
  rw [ Finset.sum_eq_add ( i ) ( finXor i s ) ] <;> simp +decide [ * ];
  · rw [ if_pos ];
    · rw [ ← dotSign_mul ];
      rw [ ← mul_assoc, dotSign_mul ];
      simp +decide [ dotSign, hsx ];
      norm_num;
    · exact hpro.2.1 i;
  · exact Ne.symm ( finXor_ne_self i s hpro.1 );
  · intro c hc₁ hc₂ hc₃; have := hpro.2.2 i c; aesop;

/-- The Gram double sum equals `2 · 2^n`. -/
theorem simon_double_sum {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n)) (s x : Fin (2 ^ n))
    (hpro : SimonPromise f s) (hsx : bdot_BV s.val x.val = false) :
    ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n),
        (if f i = f k then dotSign i.val x.val * dotSign k.val x.val else 0)
      = (2 * 2 ^ n : ℂ) := by
  convert Finset.sum_congr rfl fun i hi => simon_inner_sum f s x hpro hsx i using 1;
  norm_num [ mul_comm ]

/-
The Gram matrix of the post-measurement amplitude vector is
    `(1 / 2^{n-1}) • 1`.
-/
theorem simonVec_gram {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n)) (s x : Fin (2 ^ n))
    (hpro : SimonPromise f s) (hsx : bdot_BV s.val x.val = false) :
    (simonVec n f x)ᴴ * (simonVec n f x)
      = ((1 : ℂ) / 2 ^ (n - 1)) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [simonVec];
  -- Expand the Gram matrix into a double sum of basis-vector inner products.
  have h_simonVec : (∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i))ᴴ * (∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i)) = (∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), (if f i = f k then dotSign i.val x.val * dotSign k.val x.val else 0 : ℂ)) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    have h_simonVec : (∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i))ᴴ * (∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i)) = ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), (dotSign i.val x.val * dotSign k.val x.val) • (stdKet (f i))ᴴ * stdKet (f k) := by
      have hstar : ∀ a b : ℕ, star (dotSign a b) = dotSign a b := by
        intro a b; unfold dotSign; split_ifs <;> simp
      simp only [conjTranspose_sum, conjTranspose_smul, Matrix.sum_mul, Matrix.mul_sum,
        smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul, hstar]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [mul_comm]
    rw [ h_simonVec, Finset.sum_smul ];
    refine' Finset.sum_congr rfl fun i hi => _;
    rw [ Finset.sum_smul ] ; congr ; ext k ; by_cases hk : f i = f k <;> simp +decide [hk] ;
    · simp +decide [ stdKet_conjTranspose, stdBra_stdKet ];
    · exact Or.inr ( by rw [ stdKet_conjTranspose, stdBra_stdKet ] ; aesop );
  rcases n <;> simp_all +decide [ pow_succ' ];
  · unfold dotSign; norm_num;
  · have := simon_double_sum f s x hpro hsx
    simp_all +decide [ ← mul_assoc, ← smul_assoc ]
    grind

/-
General: the sum of squared magnitudes of a column vector equals the real part
    of its Gram entry.
-/
theorem sum_normSq_eq_gram {m : ℕ} (M : Matrix (Fin m) (Fin 1) ℂ) :
    ∑ j : Fin m, Complex.normSq (M j 0) = ((Mᴴ * M) 0 0).re := by
  simp +decide [ Matrix.mul_apply, Complex.normSq ]

/-- Probability (squared norm) of the post-measurement amplitude vector `simonVec`
    equals `1 / 2^{n-1}` when `s · x = 0`. -/
theorem Simon_prob_vec {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n)) (s x : Fin (2 ^ n))
    (hpro : SimonPromise f s) (hsx : bdot_BV s.val x.val = false) :
    ∑ j : Fin (2 ^ n), Complex.normSq (simonVec n f x j 0) = (1 : ℝ) / 2 ^ (n - 1) := by
  rw [sum_normSq_eq_gram, simonVec_gram f s x hpro hsx]
  have h : ((1:ℂ)/2^(n-1)) = ((1/2^(n-1) : ℝ) : ℂ) := by push_cast; ring
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, h, Complex.ofReal_re]

/-- Simon measurement probability.  When `s · x = 0`, the probability of
    measuring `x` in the first register (the squared norm of the partial-measurement
    amplitude vector) equals `1 / 2^{n-1}`. -/
theorem Simon_correct_0 {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n)) (s x : Fin (2 ^ n))
    (hpro : SimonPromise f s) (hsx : bdot_BV s.val x.val = false) :
    ∑ j : Fin (1 * 2 ^ n),
        Complex.normSq
          (((stdBra x ⊗ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) * Simon_output n f) j 0)
      = (1 : ℝ) / 2 ^ (n - 1) := by
  rw [Simon_simplify]
  simp only [Matrix.submatrix_apply, id_eq]
  rw [Equiv.sum_comp (finCongr (one_mul (2 ^ n)))
      (fun j => Complex.normSq (simonVec n f x j 0))]
  exact Simon_prob_vec f s x hpro hsx

/-- Under the period promise, the probability amplitude of
    measuring any `x` with `s · x = 1` in the first register is the zero vector;
    such outcomes never occur. -/
theorem Simon_correct_1 {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n)) (s x : Fin (2 ^ n))
    (hper : HasPeriod f s) (hsx : bdot_BV s.val x.val = true) :
    (stdBra x ⊗ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) * Simon_output n f = 0 := by
  rw [Simon_simplify, simonVec_eq_zero f s x hper hsx]
  simp


/-! ## Correctness_s ≠ 0 -/

/-
Inner sum for injective `f`: for fixed `i`, the only `k` with `f i = f k` is
`k = i`, so the Gram weights sum to `(-1)^{i·x}·(-1)^{i·x} = 1`.
-/
theorem simon_inner_sum_injective {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n))
    (hinj : Function.Injective f) (x i : Fin (2 ^ n)) :
    ∑ k : Fin (2 ^ n),
        (if f i = f k then dotSign i.val x.val * dotSign k.val x.val else 0) = 1 := by
  simp +decide [ hinj.eq_iff, dotSign ];
  split_ifs <;> norm_num

/-
The Gram double sum for injective `f` equals `2^n`.
-/
theorem simon_double_sum_injective {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n))
    (hinj : Function.Injective f) (x : Fin (2 ^ n)) :
    ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n),
        (if f i = f k then dotSign i.val x.val * dotSign k.val x.val else 0)
      = (2 ^ n : ℂ) := by
  convert Finset.sum_congr rfl fun i hi => simon_inner_sum_injective f hinj x i using 1;
  norm_num

/-
The Gram matrix of the post-measurement amplitude vector for injective `f` is
    `(1 / 2^n) • 1`.
-/
theorem simonVec_gram_injective {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n))
    (hinj : Function.Injective f) (x : Fin (2 ^ n)) :
    (simonVec n f x)ᴴ * (simonVec n f x)
      = ((1 : ℂ) / 2 ^ n) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  -- Expand the definitions of simonVec, then apply simonVec_gram.
  simp [simonVec] at *;
  -- Expand the Gram product using the definition of `simonVec`.
  have h_expand : (∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i))ᴴ * (∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i)) = (∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), (if f i = f k then dotSign i.val x.val * dotSign k.val x.val else 0) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    -- By definition of conjugate transpose, we can expand the left-hand side.
    have h_conj_transpose : (∑ i : Fin (2 ^ n), dotSign i.val x.val • stdKet (f i))ᴴ = ∑ i : Fin (2 ^ n), dotSign i.val x.val • stdBra (f i) := by
      ext i j; simp +decide [Matrix.sum_apply] ;
      refine' Finset.sum_congr rfl fun i _ => _ ; unfold dotSign ; simp +decide [ stdKet, stdBra ] ; ring;
      split_ifs <;> norm_num [ Complex.ext_iff ];
    simp_all +decide [Matrix.mul_sum, Matrix.sum_mul, Finset.sum_ite];
    simp +decide [Finset.sum_smul, stdBra_stdKet, hinj.eq_iff];
    simp +decide [Finset.sum_filter, smul_smul];
  convert congr_arg ( fun m : Matrix ( Fin 1 ) ( Fin 1 ) ℂ => ( 2 ^ n : ℂ ) ⁻¹ • m ) h_expand using 1 ; norm_num [ simon_double_sum_injective f hinj x ]

/-- Probability (squared norm) of the post-measurement amplitude vector `simonVec`
    equals `1 / 2^n` for injective `f` (the `s = 0` case): the measurement
    distribution over the first register is uniform. -/
theorem Simon_prob_vec_injective {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n))
    (hinj : Function.Injective f) (x : Fin (2 ^ n)) :
    ∑ j : Fin (2 ^ n), Complex.normSq (simonVec n f x j 0) = (1 : ℝ) / 2 ^ n := by
  rw [sum_normSq_eq_gram, simonVec_gram_injective f hinj x]
  have h : ((1:ℂ)/2^n) = ((1/2^n : ℝ) : ℂ) := by push_cast; ring
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, h, Complex.ofReal_re]

/-- **Simon measurement probability, case `s = 0`.**  When `f` is injective (the
    degenerate `s = 0` case where Simon's promise is not satisfied), every outcome
    `x` in the first register is measured with the uniform probability `1 / 2^n`. -/
theorem Simon_prob_injective {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ n))
    (hinj : Function.Injective f) (x : Fin (2 ^ n)) :
    ∑ j : Fin (1 * 2 ^ n),
        Complex.normSq
          (((stdBra x ⊗ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) * Simon_output n f) j 0)
      = (1 : ℝ) / 2 ^ n := by
  rw [Simon_simplify]
  simp only [Matrix.submatrix_apply, id_eq]
  rw [Equiv.sum_comp (finCongr (one_mul (2 ^ n)))
      (fun j => Complex.normSq (simonVec n f x j 0))]
  exact Simon_prob_vec_injective f hinj x

end DiracRepr
end
