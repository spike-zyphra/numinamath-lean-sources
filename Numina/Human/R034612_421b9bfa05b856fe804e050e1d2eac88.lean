import Mathlib

/-Find the smallest integer $n$ for which the sum of the integers from $-25$ to $n$ (including $-25$ and $n$) is at least $26$.-/
theorem algebra_20376 : IsLeast {n | ∑ i in Finset.Icc (-25) n, i ≥ 26} 26 := by
  -- auxiliary lemma : -a + ... + 0 + ... + a = 0 holds for any non-negative integers.
  have aux {a : ℤ} (ha : 0 ≤ a) : ∑ i in Finset.Icc (-a) a, i = 0 := by
    apply Int.le_induction (m := 0) ?_ ?_ a ha
    simp
    intro n nneg ih
    have : Finset.Icc (-(n + 1)) (n + 1) = Finset.Icc (-n) n ∪ {n + 1} ∪ {-(n + 1)} := by
      ext x; constructor <;> simp <;> omega
    rw [this, Finset.sum_union, Finset.sum_union, ih]
    all_goals simp
    linarith
    omega
  -- Compute that ∑ i ∈ Finset.Icc (-25) 26, i = 26.
  have aux1 : 26 = ∑ i ∈ Finset.Icc (-25) 26, i := by
    have : Finset.Icc (-25) 26 = Finset.Icc (-25) 25 ∪ {26} := by
      ext x; constructor <;> simp <;> omega
    rw [this, Finset.sum_union]
    simp [aux (show 0 ≤ 25 by omega)]
    simp
  constructor <;> simp [lowerBounds]
  · -- by the above lemma, this is obvious.
    simp [←aux1]
  · intro a h
    -- if a b are non-negative integers, then `∑ i ∈ Finset.Icc (-25) a, i ≤ ∑ i ∈ Finset.Icc (-25) b`
    -- implies that $a \le b$.
    have h1 {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
      ∑ i ∈ Finset.Icc (-25) a, i ≤ ∑ i ∈ Finset.Icc (-25) b, i → a ≤ b:= by
        intro hh
        contrapose! hh
        have : Finset.Icc (-25) a  = Finset.Icc (-25) b ∪ Finset.Ioc b a := by
           ext x; constructor <;> simp <;> omega
        rw [this, Finset.sum_union]
        simp
        apply Finset.sum_pos
        simp
        omega
        simp [hh]
        simp [Finset.disjoint_iff_ne]
        omega
    -- consider whether $0 \le a$.
    by_cases apos : 0 ≤ a
    · rw [aux1] at h
      exact h1 (by omega) (by omega) h
    · push_neg at apos
      have : ∑ i ∈ Finset.Icc (-25) a, i ≤ 0 := by
        apply Finset.sum_nonpos
        simp
        omega
      linarith
