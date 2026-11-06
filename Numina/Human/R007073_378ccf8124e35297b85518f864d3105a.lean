import Mathlib

/- Provide an alternative proof of the division algorithm using the well-ordering property. (Hint: When dividing \( a \) by \( b \), consider the remainder to be the least positive integer in the set of integers of the form \( a - qb \) for integers \( q \).)-/
theorem number_theory_4757 {a b : ℤ} (hb : 0 < b) : ∃ q, ∃ r, a=q*b+r ∧ 0 ≤ r ∧ r < b ∧
    (∀ q' r', (a=q'*b+r' ∧ 0 ≤ r' ∧ r' < b) → (q'=q ∧ r'=r)):= by
  /- 原答案错误，以下为重写的正确证明。 -/
  let S : Set ℕ := {r : ℕ | ∃ q : ℤ, a = q * b + r}
  have sne : S.Nonempty := by
    rcases lt_or_ge a 0 with _ | ha
    /- 当a<0时，需要利用整数的阿基米德性 -/
    . obtain ⟨q, hq⟩ := Archimedean.arch (-a) hb
      simp at hq
      use (a + q*b).natAbs
      use -q
      have : 0 ≤ a+q*b := by linarith
      rw [Int.natAbs_of_nonneg this]
      ring
    /- 当a≥0时，取q=0，可知r=a∈S -/
    . use a.natAbs
      use 0
      simp
      symm
      exact abs_of_nonneg ha
  /- 利用自然数的良基性从S中选取最小值 -/
  set r := Nat.lt_wfRel.wf.min S sne
  have r_mem_S : r ∈ S := Nat.lt_wfRel.wf.min_mem S sne
  obtain ⟨q, hq⟩ := r_mem_S
  use q, r
  /- 因为r是S的最小值，故有`r<b` -/
  have hrb : r < b := by
    suffices r < b.natAbs by
      rw [← abs_of_pos hb, ← Int.natCast_natAbs]
      norm_cast
    by_contra h
    push_neg at h
    have : r - b.natAbs ∈ S := by
      simp [S]
      use (q + 1)
      rw [Int.ofNat_sub h, hq, Int.natCast_natAbs, abs_of_pos hb]
      ring
    have : ¬(r - b.natAbs < r) := Nat.lt_wfRel.wf.not_lt_min S sne this
    have : r - b.natAbs < r := by
      simp
      refine ⟨?_, hb.ne'⟩
      refine lt_of_lt_of_le ?_ h
      simpa using hb.ne'
    contradiction
  refine ⟨hq, Int.ofNat_zero_le r, ⟨hrb, ?_⟩⟩
  /- 以下证明q,r的唯一性 -/
  intro q' r' hq'r'
  have hq' : (q' - q)*b = r - r' := by linear_combination hq - hq'r'.1
  rcases lt_trichotomy (q' - q) 0 with h | h | h
  /- 当q'-q<0时，-b≥r-r'，这是矛盾的！ -/
  . have : -b ≥ r - r' := by rw [← hq']; nlinarith
    have : -b < r - r' := by linarith
    linarith
  . rw [h, zero_mul, eq_comm] at hq'
    rw [sub_eq_zero] at h hq'
    exact ⟨h, hq'.symm⟩
  /- 当q'-q>0时，b≤r-r'，这是矛盾的！ -/
  . have : b ≤ r - r' := by rw [← hq']; nlinarith
    have : r - r' < b := by linarith
    linarith
