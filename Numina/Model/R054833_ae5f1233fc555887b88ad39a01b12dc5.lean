import Mathlib

theorem algebra_12885 (n : ℕ) (h₀ : n > 0) (h₁ : ∑ i ∈ Finset.range n, (2 * i + 1) = 100) :
    n = 10 := by 
  have h2 : n ≤ 10 := by
    by_contra h
    push_neg at h
    have h3 : n > 10 := by linarith
    have h4 : ∑ i in Finset.range n, (2 * i + 1) > 100 := by
      have h5 : n ≥ 11 := by linarith
      have h9 : ∀ k : ℕ, k ≥ 1 → ∑ i in Finset.range k, (2 * i + 1) = k * k := by
        intro k h_k
        induction k with
        | zero =>
          exfalso
          linarith
        | succ k ih =>
          cases k with
          | zero => simp
          | succ k => 
            rw [Finset.sum_range_succ]
            rw [ih (by linarith)]
            simp [Nat.add_assoc]
            <;> ring_nf
            <;> linarith
      have h10 : ∑ i in Finset.range n, (2 * i + 1) = n * n := by 
        apply h9 
        linarith
      have h11 : n * n ≥ 121 := by 
        nlinarith
      linarith [h10, h₁]
    linarith [h₁, h4]
  interval_cases n <;> try { 
    norm_num [Finset.sum_range_succ] at h₁ <;> all_goals tauto
  }
  <;> contradiction