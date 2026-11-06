import Mathlib

variable {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hkp : k < p)

include hp hk hkp in
/-- Auxiliary lemma : $\binom {p-1} k \equiv -\binom {p-1} {k-1} \pmod{p}$. -/
lemma aux0 : (Nat.choose (p - 1) k : ℤ) ≡ - (Nat.choose (p - 1) (k - 1)) [ZMOD p] := by
  have h1 := Nat.choose_eq_choose_pred_add (Nat.Prime.pos hp) hk
  have h2 : 0 ≡ (p - 1).choose (k - 1) + (p - 1).choose k [ZMOD p] := by
    have h3 : p.choose k ≡ 0 [ZMOD p] := by
      simp [Int.modEq_zero_iff_dvd]; norm_cast;
      exact Nat.Prime.dvd_choose_self hp (by linarith [hk]) hkp
    exact h3.symm.trans (by simp [h1])
  have := Int.ModEq.add h2.symm (Int.ModEq.refl (- ((p-1).choose k : ℤ)))
  simp at this
  convert Int.ModEq.mul (Int.ModEq.refl (-1)) (this.symm) using 1 <;> simp

include hp hk hkp in
/-- Auxiliary lemma : $\binom {p-1} k \equiv (-1)^k \pmod {p}$. -/
lemma aux0'  : Nat.choose (p - 1) k ≡ (-1) ^ k [ZMOD p] := by
  generalize hkk : k = kk
  revert k
  induction' kk with kk ih <;> intro k h1 h2 h3
  · linarith
  · by_cases tri : kk = 0
    · symm; simp [tri, Int.modEq_iff_dvd]; norm_cast
      simp [Nat.sub_add_cancel (Nat.add_one_le_of_lt <| Nat.Prime.pos hp)]
    · have h4 := ih (Nat.pos_of_ne_zero tri) (by linarith) rfl
      have := aux0 hp h1 h2
      simp [h3] at this
      have h5 : (p - 1).choose kk ≡ - (p - 1).choose (kk + 1) [ZMOD p] := by
        convert Int.ModEq.mul (Int.ModEq.refl (-1)) this.symm using 1 <;> simp
      have h6 := h5.symm.trans h4
      convert Int.ModEq.mul (Int.ModEq.refl (-1)) h6 <;> ring


include hp hk hkp in
/-- (1) : Let $p$ be a prime number. Prove that
  $\binom{p-1}{k}^{2}-1$ is divisible by $p$. -/
theorem number_theory_4061_1 : p ∣ ((p - 1).choose k) ^ 2 - 1:= by
  nth_rw 2 [show 1 = 1 ^ 2 by linarith]
  -- Rewrite $\binom{p-1}{k}^{2}-1$ as $(\binom{p-1}{k} + 1) * (\binom{p-1}{k} - 1) $.
  rw [Nat.sq_sub_sq]
  have := (aux0' hp hk hkp).symm
  rcases Nat.even_or_odd k with evenk | oddk
  · -- If $k$ is even, $\binom {p-1} k \equiv 1 \pmod{p}$.
    -- Thus, $$\binom {p-1} k -1 \equiv 1-1 \equiv 0 \pmod{p} $$.
    simp [evenk, Int.modEq_iff_dvd] at this
    apply Dvd.dvd.mul_left
    convert this
    constructor <;> intro h <;> norm_cast
    rw [show 1 = ((1 : ℕ) : ℤ) by simp] at h
    rw [←Int.natCast_sub, Int.natCast_dvd_natCast] at h
    exact h
    linarith [Nat.choose_pos (show k ≤ p - 1 from Nat.le_sub_one_of_lt hkp)]
  · -- If $k$ is odd, $\binom {p-1} k \equiv -1 \pmod{p}$.
    -- Thus, $$\binom {p-1} k +1 \equiv -1+1 \equiv 0 \pmod{p} $$.
    simp [oddk, Int.modEq_iff_dvd] at this
    apply Dvd.dvd.mul_right
    rw [show 1 = ((1 : ℕ) : ℤ) by simp] at this
    rw [←Int.natCast_add, Int.natCast_dvd_natCast] at this
    exact this

include hp in
/-- (2.1) Let $p$ be a prime number. Prove that
$\binom{p-1}{0}^{s}+\binom{p-1}{1}^{s}+\binom{p-1}{2}^{s}+\cdots+\binom{p-1}{p-1}^{s}$ is divisible by $p$ if $s$ is even. -/
theorem number_theory_2_1 : Even s → p ∣ ∑ k in Finset.range p, ((p - 1).choose k) ^ s := by
  intro hs
  rw [Nat.dvd_iff_mod_eq_zero, Finset.sum_nat_mod]
  -- If s is even, $(\binom {p-1} k)^s \equiv 1 \pmod {p} \text{for all k}$.
  have h1 : ∀ i ∈ Finset.range p, (p - 1).choose i ^ s % p = 1 := by
    intro i hi
    have : (p - 1).choose i ^ s ≡ 1 [ZMOD p] := by
      by_cases itri : i = 0
      · simp [itri]
      · have := aux0' hp ( Nat.pos_of_ne_zero itri) (Finset.mem_range.1 hi)
        convert Int.ModEq.pow s this
        rw [←pow_mul,mul_comm, pow_mul]
        simp [hs]
    convert this
    simp [Int.ModEq]
    norm_cast
    rw  [Nat.one_mod_eq_one.2 (Nat.Prime.ne_one hp)]
  simp [Finset.sum_eq_card_nsmul h1]

/-- Define s1 as the set of even natural numbers less than $2p+1$. -/
def s1 (p : ℕ) := {x | x ∈ Finset.range (2 * p + 1) ∧ Even x}
/-- Define s2 as the set of odd natural numbers less than $2p+1$. -/
def s2 (p : ℕ) := {x | x ∈ Finset.range (2 * p + 1) ∧ Odd x}


lemma s1Finite (p : ℕ) : (s1 p).Finite :=
  Set.Finite.subset (Finset.finite_toSet (Finset.range (2 * p + 1))) (fun _ h1 => h1.1)
lemma s2Finite (p : ℕ) : (s2 p).Finite :=
  Set.Finite.subset (Finset.finite_toSet (Finset.range (2 * p + 1))) (fun _ h1 => h1.1)

lemma s2succ (p : ℕ) : (s2Finite (p + 1)).toFinset = insert (2 * p + 1) (s2Finite p).toFinset := by
  simp [Finset.insert_eq]
  ext y; simp [s2]
  constructor <;> intro h
  · by_cases hy : y = 2 * p + 1
    · exact Or.inl hy
    · have : y ≠ 2 * (p + 1) := by
        intro h1; exact Nat.not_odd_iff_even.2 (⟨p + 1, by linarith⟩) h.2
      right; exact ⟨by omega, h.2⟩
  · rcases h with h1 | h2 <;> aesop
    linarith

/-- Auxiliary lemma : the union of sets `s1` and `s2` equal `Finset.range (2 * p + 1)`. -/
lemma s1_union_s2 : (s1Finite p).toFinset ∪ (s2Finite p).toFinset = Finset.range (2 * p + 1) := by
  ext x; simp [s1, s2];
  constructor <;> intro h <;> aesop; exact Nat.even_or_odd x

/-- Auxiliary lemma : `s1` and `s2` are disjoint. -/
lemma disjoints1s2 : Disjoint (s1Finite p).toFinset (s2Finite p).toFinset := by
    simp [Finset.disjoint_left]
    intro a h1 h2
    exact Nat.not_odd_iff_even.2 h1.2 h2.2

/-- Auxiliary lemma : the number of elements of `s2` is $p$. -/
lemma card_s2_of_range_odd (p : ℕ) : (s2Finite p).toFinset.card = p := by
  generalize hp : p = n
  revert p
  induction' n with n ih
  · simp [s2]; ext x; simp [Set.mem_setOf]; tauto
  · intro p _
    simp [s2succ]
    rw [Finset.card_insert_of_not_mem, ih n rfl]
    simp [s2]

/-- Auxiliary lemma : the number of elements of `s1` is $p+1$. -/
lemma card_s1_of_range_odd (p : ℕ) : (s1Finite p).toFinset.card = p + 1:= by
  have h1 := Finset.card_union_of_disjoint disjoints1s2 (s := (s1Finite p).toFinset) (t := (s2Finite p).toFinset)
  simp [card_s2_of_range_odd, s1_union_s2] at h1
  linarith

include hp in
/-- (2.2) Let $p$ be a prime number. Prove that
$\binom{p-1}{0}^{s}+\binom{p-1}{1}^{s}+\binom{p-1}{2}^{s}+\cdots+\binom{p-1}{p-1}^{s}$ is divisible by $p$ leaves a remainder of 1 if $s$ is odd. -/
theorem number_theory_2_2 (hpp : Odd p) : Odd s → (∑ k in Finset.range p, ((p - 1).choose k) ^ s) % (p : ℤ) = 1 := by
  intro hs
  obtain ⟨n, hn⟩ := hpp
  have nne0 : n ≠ 0 := by intro hn1; simp [hn1] at hn; exact Nat.Prime.ne_one hp hn
  have eq0 : ∀ x ∈ (s1Finite n).toFinset, ((2 * n).choose x ^ s : ℤ) % (2 * n  + 1) = 1 := by
    intro x hx
    have : (p - 1).choose x ^ s ≡ 1 [ZMOD p] := by
      by_cases itri : x = 0
      · simp [itri]
      · simp [s1] at hx
        have := aux0' hp ( Nat.pos_of_ne_zero itri) (by convert hx.1)
        simp [hx.2] at this
        convert Int.ModEq.pow s this
        simp
    simp [hn, Int.ModEq] at this; simp [this]; norm_cast
    simp [Nat.one_mod_eq_one]; exact Nat.pos_of_ne_zero nne0
  have eq1 : ∀ x ∈ (s2Finite n).toFinset, ((p - 1).choose x ^ s : ℤ) % (p : ℤ) = p - 1 := by
    intro x hx
    have : (p - 1).choose x ^ s ≡ -1 [ZMOD p] := by
      simp [s2] at hx
      have := aux0' hp (show 0 < x from Nat.pos_of_ne_zero (fun h => by simp [h] at hx)) (by convert hx.1)
      simp [hx.2] at this
      convert Int.ModEq.pow s this
      simp [hs]
    simp [Int.ModEq] at this; simp [this, Int.neg_emod]
    refine Int.emod_eq_of_lt (by simp [Nat.Prime.one_le hp]) (by simp)
  simp only [hn, Nat.add_sub_cancel, congrArg, Int.natCast_add] at eq0 eq1
  rw [show ((1 : ℕ) : ℤ) = 1 by rfl, Int.add_sub_cancel] at eq1
  have h1 : ∑ a ∈ (s1Finite n).toFinset, ((2 * n).choose a : ℤ) ^ s % (2 * n  + 1) = (s1Finite n).toFinset.card • 1 :=
    Finset.sum_eq_card_nsmul eq0
  have h2 : ∑ a ∈ (s2Finite n).toFinset, ((2 * n).choose a : ℤ) ^ s % (2 * n  + 1) = (s2Finite n).toFinset.card • (2 * n):=
    Finset.sum_eq_card_nsmul eq1
  simp [hn]
  rw [←s1_union_s2, Finset.sum_union disjoints1s2]
  rw [Int.add_emod, Finset.sum_int_mod, h1, Finset.sum_int_mod, h2]
  simp [card_s2_of_range_odd, card_s1_of_range_odd]; norm_cast;
  rw [add_rotate, add_assoc, show n * (2 * n) + n = n * (2 * n + 1) by rfl]
  simp [Nat.one_mod_eq_one]; exact Nat.pos_of_ne_zero nne0
