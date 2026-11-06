import Mathlib

-- Let $N$ be a positive integer. Let $d$ be a randomly chosen positive divisor of $N$. Determine the expected value of $\frac{d^2}{d^2 + N}$. Show the answer is $\frac{1}{2}$.

theorem number_theory_641391 {N : ℕ} (hN : N > 0) :
    ∑ d ∈ N.divisors, (d ^ 2 / (d ^ 2 + N : ℝ)) / N.divisors.card = 1 / 2 := by

  have : N.divisors.card ≠ 0 := by
    by_contra h
    simp at h
    omega

  rw [← Finset.sum_div]
  field_simp
  rw [mul_two]

  have := Nat.sum_div_divisors N (fun d => (d ^ 2 / (d ^ 2 + N : ℝ)))
  nth_rw 2 [← this]

  rw [← Finset.sum_add_distrib]

  rw [show N.divisors.card = ∑ d ∈ N.divisors, 1 by simp]
  push_cast
  apply Finset.sum_congr rfl
  intro d hd

  have : d ≠ 0 := by
    by_contra
    subst d
    simp at hd

  have : N ≠ 0 := by omega

  let m := N / d

  rw [show N / d = m by omega]

  have : (d ^ 2 + N) ≠ 0 := by omega
  have : (m ^ 2 + N) ≠ 0 := by omega
  norm_cast



  field_simp
  ring_nf
  norm_cast
  rw [show N = d * m by
    unfold m
    rw [Nat.mul_div_cancel']
    simp at hd
    exact hd.1
  ]
  ring
