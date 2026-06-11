import Qcircuits.Simon

open Matrix Complex

noncomputable section

namespace DiracRepr

/-!
We reuse the `Uf_general`, `phaseVec`, `oracle_on_ketp_minus` from
`DeutschJozsa.lean`.
-/


/-! ## The number of marked elements -/

/-- The number of inputs marked by `f` (i.e. with `f x = true`). -/
def numMarked (n : ℕ) (f : Fin (2 ^ n) → Bool) : ℕ :=
  (Finset.univ.filter (fun x => f x = true)).card


/-! ## The "good" and "bad" subspace vectors -/

/-- The (un-normalised) uniform superposition over the **marked** states. -/
def goodVec (n : ℕ) (f : Fin (2 ^ n) → Bool) : Matrix (Fin (2 ^ n)) (Fin 1) ℂ :=
  ∑ x : Fin (2 ^ n), if f x then stdKet x else 0

/-- The (un-normalised) uniform superposition over the **unmarked** states. -/
def badVec (n : ℕ) (f : Fin (2 ^ n) → Bool) : Matrix (Fin (2 ^ n)) (Fin 1) ℂ :=
  ∑ x : Fin (2 ^ n), if f x then 0 else stdKet x

/-- `goodVec + badVec` is the full uniform (un-normalised) superposition. -/
theorem goodVec_add_badVec (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    goodVec n f + badVec n f = ∑ x : Fin (2 ^ n), stdKet x := by
  convert Finset.sum_add_distrib.symm using 1;
  exact Finset.sum_congr rfl fun _ _ => by aesop;

/-- `|ψ⟩ = |+⟩^⊗n` decomposes as `s2^n • (goodVec + badVec)`. -/
theorem ketp_n_eq_good_bad (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    ketp_n n = (s2 : ℂ) ^ n • (goodVec n f + badVec n f) := by
  rw [ goodVec_add_badVec n f, ketp_n_eq_sum n ]


/-! ## The phase oracle `O` -/

/-- The Grover phase oracle on the `n`-qubit register:
    `O = ∑_x (-1)^{f(x)} |x⟩⟨x|`, i.e. `O|x⟩ = (-1)^{f(x)}|x⟩`. -/
def groverPhase (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  ∑ x : Fin (2 ^ n), (if f x then (-1 : ℂ) else 1) • stdProj x

/-- The phase oracle flips the sign of marked basis states. -/
theorem groverPhase_stdKet (n : ℕ) (f : Fin (2 ^ n) → Bool) (y : Fin (2 ^ n)) :
    groverPhase n f * stdKet y = (if f y then (-1 : ℂ) else 1) • stdKet y := by
  -- By definition of groverPhase, we can expand the product using the linearity of matrix multiplication.
  have h_expand : groverPhase n f * stdKet y = ∑ x : Fin (2 ^ n), (if f x then (-1 : ℂ) else 1) • (stdProj x * stdKet y) := by
    unfold groverPhase;
    simp +decide [Matrix.sum_mul];
    exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> simp +decide [ * ] ;
  rw [ h_expand, Finset.sum_eq_single y ] <;> simp +contextual [ stdProj_stdKet ]

/-- The phase oracle negates the good vector. -/
theorem groverPhase_goodVec (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    groverPhase n f * goodVec n f = - goodVec n f := by
  unfold goodVec; simp +decide [ Matrix.mul_sum ] ;
  rw [ ← Finset.sum_neg_distrib ] ; congr ; ext x ; split_ifs <;> simp_all +decide [ groverPhase_stdKet ] ;

/-- The phase oracle fixes the bad vector. -/
theorem groverPhase_badVec (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    groverPhase n f * badVec n f = badVec n f := by
  convert Finset.sum_congr rfl fun x _refine => ?_ using 1;
  convert Matrix.mul_sum _ _ _ using 1;
  split_ifs <;> simp_all +decide;
  convert groverPhase_stdKet n f x using 1 ; aesop


/-! ### Phase kickback: connecting `O` to the physical oracle `U_f` -/

/-- `groverPhase` applied to `|+⟩^⊗n` gives the phase-kicked vector `phaseVec`. -/
theorem groverPhase_ketp (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    groverPhase n f * ketp_n n = phaseVec n f := by
  have h_step1 : groverPhase n f * ketp_n n = (groverPhase n f) * ((s2 : ℂ) ^ n • ∑ x : Fin (2 ^ n), stdKet x) := by
    rw [ ketp_n_eq_sum ];
  rw [ h_step1, Matrix.mul_smul, Matrix.mul_sum ];
  ext i j; fin_cases j; simp +decide [ phaseVec, groverPhase_stdKet ] ;
  simp +decide [ Matrix.sum_apply, stdKet ];
  rw [ Finset.sum_eq_single i ] <;> aesop

/-- Phase kickback for the uniform superposition: `U_f (|+⟩^⊗n |−⟩) = (O|+⟩^⊗n)|−⟩`. -/
theorem grover_phase_kickback_ketp (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    Uf_general n f * (ketp_n n ⊗ ket_minus) = (groverPhase n f * ketp_n n) ⊗ ket_minus := by
  rw [ oracle_on_ketp_minus, groverPhase_ketp ]


/-! ## The diffusion operator `D` -/

/-- The Grover diffusion (inversion about the mean) operator
    `D = 2|ψ⟩⟨ψ| − I` with `|ψ⟩ = |+⟩^⊗n`. -/
def groverDiff (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (2 : ℂ) • (ketp_n n * (ketp_n n)ᴴ) - 1

/-- `⟨ψ| goodVec = (s2^n · k)` as a `1×1` matrix. -/
theorem ketpH_goodVec (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    (ketp_n n)ᴴ * goodVec n f =
      ((s2 : ℂ) ^ n * (numMarked n f : ℂ)) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  -- Prove entrywise: ext i j; fin_cases i; fin_cases j.
  ext i j
  fin_cases i
  fin_cases j
  simp [goodVec, stdKet, numMarked];
  simp +decide [ Matrix.mul_apply, Finset.sum_ite ];
  rw [ Finset.sum_congr rfl fun x _ => by rw [ ketp_n_entry_conj ] ];
  simp +decide [ketp_n_entry, Matrix.sum_apply];
  simp +decide [ Finset.sum_ite, mul_comm ]

/-- `⟨ψ| badVec = (s2^n · (N − k))` as a `1×1` matrix. -/
theorem ketpH_badVec (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    (ketp_n n)ᴴ * badVec n f =
      ((s2 : ℂ) ^ n * ((2 ^ n : ℂ) - (numMarked n f : ℂ))) •
        (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j ; fin_cases i ; fin_cases j ; simp_all +decide [Matrix.mul_apply];
  -- By definition of `badVec`, we know that `badVec n f x 0 = if f x then 0 else 1`.
  have h_badVec : ∀ x : Fin (2 ^ n), badVec n f x 0 = if f x then 0 else 1 := by
    intro x
    simp [badVec];
    simp +decide [ stdKet, Matrix.sum_apply ];
    rw [ Finset.sum_eq_single x ] <;> aesop;
  -- By definition of `ketp_n`, we know that `ketp_n n x 0 = (s2 : ℂ) ^ n`.
  have h_ketp_n : ∀ x : Fin (2 ^ n), ketp_n n x 0 = (s2 : ℂ) ^ n := fun x => ketp_n_entry n x
  simp_all +decide [ numMarked ];
  norm_num [ Finset.sum_ite, mul_comm ];
  erw [ Complex.conj_ofReal ] ; norm_num;
  rw [ eq_sub_iff_add_eq ] ; norm_cast ; rw [ Finset.card_filter, Finset.card_filter ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.sum_congr rfl fun x hx => by aesop ] ; norm_num;

/-- Diffusion acting on the good vector. -/
theorem groverDiff_goodVec (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    groverDiff n * goodVec n f =
      (2 * (numMarked n f : ℂ) / (2 ^ n : ℂ) - 1) • goodVec n f
        + (2 * (numMarked n f : ℂ) / (2 ^ n : ℂ)) • badVec n f := by
  convert congr_arg ( fun x : Matrix ( Fin ( 2 ^ n ) ) ( Fin 1 ) ℂ => ( ( 2:ℂ ) • ( ketp_n n * ( ketp_n n ) ᴴ * x ) - x ) ) ( rfl : goodVec n f = goodVec n f ) using 1;
  · unfold groverDiff; norm_num [ Matrix.sub_mul ] ;
  · rw [ show ketp_n n * ( ketp_n n ) ᴴ * goodVec n f = ( ( s2 : ℂ ) ^ n * ( numMarked n f : ℂ ) ) • ketp_n n from ?_ ];
    · rw [ ketp_n_eq_good_bad ];
      ext i j ; norm_num ; ring;
      norm_cast ; norm_num [ pow_mul' ] ; ring;
      norm_num only [ mul_assoc, ← mul_pow ];
    · rw [ Matrix.mul_assoc, ketpH_goodVec ];
      rw [ Matrix.mul_smul, Matrix.mul_one ]

/-- Diffusion acting on the bad vector. -/
theorem groverDiff_badVec (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    groverDiff n * badVec n f =
      (2 * ((2 ^ n : ℂ) - (numMarked n f : ℂ)) / (2 ^ n : ℂ)) • goodVec n f
        + (2 * ((2 ^ n : ℂ) - (numMarked n f : ℂ)) / (2 ^ n : ℂ) - 1) • badVec n f := by
  convert congr_arg ( fun x : Matrix ( Fin ( 2 ^ n ) ) ( Fin 1 ) ℂ => ( ( 2:ℂ ) • ( ketp_n n * ( ( ketp_n n ) ᴴ * badVec n f ) ) - badVec n f ) ) ( funext fun i => rfl ) using 1;
  · unfold groverDiff;
    norm_num [ Matrix.sub_mul, Matrix.mul_assoc ];
  · convert congr_arg ( fun x : Matrix ( Fin ( 2 ^ n ) ) ( Fin 1 ) ℂ => ( ( 2:ℂ ) • ( ( s2:ℂ ) ^ n * ( ( 2 ^ n:ℂ ) - ( numMarked n f:ℂ ) ) ) • ketp_n n - badVec n f ) ) ( funext fun i => rfl ) using 1;
    · rw [ ketp_n_eq_good_bad ] ; ext i j ; norm_num ; ring;
      norm_cast ; norm_num [ pow_mul', ← mul_pow ] ; ring;
      norm_num [ pow_mul', ← mul_pow ];
      norm_num [ mul_assoc, ← mul_pow ];
    · rw [ ketpH_badVec ];
      norm_num [ Matrix.mul_smul, Matrix.smul_mul ];
    · exact fun _ _ => 0;
  · exact fun _ _ => 0


/-! ## The Grover iterate and the subspace dynamics -/

/-- One Grover iteration `G = D · O`. -/
def groverStep (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  groverDiff n * groverPhase n f

/-- A state in the 2D subspace: `a·goodVec + b·badVec`. -/
def groverState (n : ℕ) (f : Fin (2 ^ n) → Bool) (a b : ℂ) :
    Matrix (Fin (2 ^ n)) (Fin 1) ℂ :=
  a • goodVec n f + b • badVec n f

/-- The linear map on coefficients `(a, b)` induced by one Grover step. -/
def groverMap (n : ℕ) (f : Fin (2 ^ n) → Bool) : ℂ × ℂ → ℂ × ℂ :=
  fun p =>
    let k : ℂ := (numMarked n f : ℂ)
    let N : ℂ := (2 ^ n : ℂ)
    (p.1 * (1 - 2 * k / N) + p.2 * (2 * (N - k) / N),
      -p.1 * (2 * k / N) + p.2 * ((N - 2 * k) / N))

/-
**One Grover step on the 2D subspace.**  `G (a·good + b·bad)` is again of the
    form `a'·good + b'·bad` with `(a', b') = groverMap (a, b)`.
-/
theorem groverStep_groverState (n : ℕ) (f : Fin (2 ^ n) → Bool) (a b : ℂ) :
    groverStep n f * groverState n f a b =
      groverState n f (groverMap n f (a, b)).1 (groverMap n f (a, b)).2 := by
  unfold groverStep groverState groverMap;
  rw [ Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul ];
  rw [ Matrix.mul_assoc, Matrix.mul_assoc ];
  rw [ groverPhase_goodVec, groverPhase_badVec ];
  rw [ Matrix.mul_neg, groverDiff_goodVec, groverDiff_badVec ] ; ring;
  ext i j ; norm_num ; ring;
  norm_num [ mul_assoc, ← mul_pow ] ; ring

/-
The initial state `|ψ⟩` as a 2D-subspace state with coefficients `(s2^n, s2^n)`.
-/
theorem groverState_ketp (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    ketp_n n = groverState n f ((s2 : ℂ) ^ n) ((s2 : ℂ) ^ n) := by
  unfold groverState; rw [ ketp_n_eq_good_bad ] ;
  rw [ smul_add ]

/-- The coefficient pair after `i` Grover iterations starting from `|ψ⟩`. -/
def groverCoeff (n : ℕ) (f : Fin (2 ^ n) → Bool) (i : ℕ) : ℂ × ℂ :=
  (groverMap n f)^[i] ((s2 : ℂ) ^ n, (s2 : ℂ) ^ n)

/-
**Closed form for the iterated state.**  After `i` Grover iterations the
    state is `groverCoeff i .1 · good + groverCoeff i .2 · bad`.
-/
theorem groverIter_eq (n : ℕ) (f : Fin (2 ^ n) → Bool) (i : ℕ) :
    (groverStep n f) ^ i * ketp_n n =
      groverState n f (groverCoeff n f i).1 (groverCoeff n f i).2 := by
  induction i <;> simp_all +decide [pow_succ'];
  · convert groverState_ketp n f using 1;
  · rw [ Matrix.mul_assoc, ‹groverStep n f ^ _ * ketp_n n = _›, groverStep_groverState ];
    unfold groverCoeff; simp +decide [ Function.iterate_succ_apply' ] ;


/-! ## Measurement amplitudes -/

/-- `⟨z| goodVec = 1` if `z` is marked, else `0`. -/
theorem stdBra_goodVec (n : ℕ) (f : Fin (2 ^ n) → Bool) (z : Fin (2 ^ n)) :
    stdBra z * goodVec n f = if f z then (1 : Matrix (Fin 1) (Fin 1) ℂ) else 0 := by
  have h_expand : stdBra z * goodVec n f = ∑ x : Fin (2 ^ n), (if f x then stdBra z * stdKet x else 0) := by
    unfold goodVec;
    simp +decide [ Matrix.mul_sum, Finset.sum_ite ];
  simp [h_expand, stdBra_stdKet];
  rw [ Finset.sum_eq_single z ] <;> aesop

/-- `⟨z| badVec = 1` if `z` is unmarked, else `0`. -/
theorem stdBra_badVec (n : ℕ) (f : Fin (2 ^ n) → Bool) (z : Fin (2 ^ n)) :
    stdBra z * badVec n f = if f z then 0 else (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  convert Finset.sum_eq_single z ( fun x _ => ?_ ) ?_ using 1;
  convert Matrix.mul_sum _ _ _;
  · split_ifs <;> simp +decide [ *, stdBra_stdKet ];
  · split_ifs <;> simp_all +decide;
    exact fun h => by rw [ stdBra_stdKet ] ; aesop;
  · aesop

/-- Grover amplitude at a marked state. -/
theorem grover_amplitude (n : ℕ) (f : Fin (2 ^ n) → Bool) (i : ℕ)
    (z : Fin (2 ^ n)) (hz : f z = true) :
    stdBra z * ((groverStep n f) ^ i * ketp_n n) =
      (groverCoeff n f i).1 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  convert congr_arg ( fun x : Matrix ( Fin ( 2 ^ n ) ) ( Fin 1 ) ℂ => stdBra z * x ) ( groverIter_eq n f i ) using 1;
  simp +decide [ groverState, Matrix.mul_add, Matrix.mul_smul ];
  rw [ stdBra_goodVec, stdBra_badVec ] ; aesop

/-- Grover amplitude at an unmarked state. -/
theorem grover_amplitude_unmarked (n : ℕ) (f : Fin (2 ^ n) → Bool) (i : ℕ)
    (z : Fin (2 ^ n)) (hz : f z = false) :
    stdBra z * ((groverStep n f) ^ i * ketp_n n) =
      (groverCoeff n f i).2 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [ groverIter_eq, groverState ];
  simp_all +decide [ Matrix.mul_add, Matrix.mul_smul ];
  rw [ stdBra_goodVec, stdBra_badVec ] ; aesop

end DiracRepr
end
