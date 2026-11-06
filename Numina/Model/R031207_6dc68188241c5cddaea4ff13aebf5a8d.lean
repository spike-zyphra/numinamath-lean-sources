import Mathlib

theorem algebra_263944 (a : ℕ → ℤ) (h₀ : ∀ n, a (n + 1) = a n + 1)
    (h₁ : ∑ i in Finset.range 2010, a i = 5307) :
    ∑ i in Finset.range 1005, a (2 * i) = 2151 := by 
  have h2 : ∀ n, a (n + 1) = a n + 1 := h₀
  have eq1 : ∀ (n : ℕ), a n = a 0 + (n : ℤ) := by 
    intro n
    induction n with
    | zero => 
      simp
    | succ n ih =>
      have h_eq : a (n + 1) = a n + 1 := h₀ n
      simp [h_eq, ih]
      <;> ring
  have h_eq : ∀ (n : ℕ), a n = a 0 + (n : ℤ) := eq1
  have h3 :  ∑ i in Finset.range 2010, a i = 2010 * a 0 + (2009 * 1005 : ℤ) := by 
    rw [Finset.sum_congr rfl (fun i hi => h_eq i)]
    -- split the sum into sum of a 0 and sum of i from 0 to 2009
    norm_num [Finset.sum_add_distrib, Finset.sum_range_succ]
    <;> try ring_nf <;> try omega
  rw [h3] at h₁
  have h4 :  ∑ i in Finset.range 1005, a (2 * i) = 1005 * a 0 + (1004 * 1005 : ℤ) := by
    -- write a (2i) using h_eq, sum over i in range 1005.
    rw [Finset.sum_congr rfl (fun i hi => show a (2 * i) = a 0 + ((2 * i : ℕ) : ℤ) by 
      apply h_eq 
     )]
    -- compute sum of a0 : 1005 * a0 + sum of i from 0 to 1004 of 2*i
    -- need to split it
    norm_num [Finset.sum_add_distrib, Finset.sum_range_succ]
    <;> try ring_nf <;> try omega
  linarith [h₁, h4]