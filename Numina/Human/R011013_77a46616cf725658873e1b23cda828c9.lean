import Mathlib
open Real

/- 4. Let $m, n$ be positive integers, then $\sum_{k=0}^{m-1} \cos \frac{2 k \pi}{m}+\sum_{k=0}^{n-1} \sin \frac{2 k \pi}{n}=$ -/

lemma lemma_1 (n:ℕ) (hn:n>0) : ∑ k ∈ Finset.range n, sin (2*k*π/n) = 0 := by -- Prove the formula for summing the sine arithmetic sequence
  have h1 (k:ℕ) (hk:k ∈ Finset.range n) : sin (2*k*π/n) = 1/(2*sin (π/n))*(-cos ((2*↑(k+1)-1)*π/n)-(-cos ((2*k-1)*π/n))) := by -- Using the integration and difference formula to analyze the cracking term of the general term
    if h:n=1 then simp_all else
    have h1:n≥1:= by linarith
    simp [le_iff_eq_or_lt] at h1
    match h1 with
    |Or.inl h =>
    have := h.symm
    contradiction
    |Or.inr h =>
    have h2 : n ≥ 2 := by linarith
    have h1 : π/n∈Set.Ioo 0 π := by
      simp
      constructor
      -- 0 < π / ↑n
      simp [pi_pos]
      linarith
      -- π / ↑n < π
      nth_rw 2 [show π=π/1 by simp]
      rw [div_lt_div_iff_of_pos_left]
      simp; exact h
      exact pi_pos
      simp; exact hn
      simp
    have := sin_pos_of_mem_Ioo h1
    field_simp
    have {a b:ℝ}:-a+b=b-a:= by linarith
    rw [this]
    rw [cos_sub_cos]
    ring_nf
    rw [sin_neg]
    ring
  rw [Finset.sum_congr rfl h1]
  rw [←Finset.mul_sum (Finset.range n) (fun x => (- cos ((2 * ↑(x+1) - 1) * π / ↑n)-(-cos ((2 * ↑x - 1) * π / ↑n)))) (1 / (2 * sin (π / ↑n)))]
  suffices h2 : ∑ i ∈ Finset.range n, ( - cos ((2 * ↑(i+1) - 1) * π / ↑n)-(-cos ((2 * ↑i - 1) * π / ↑n))) = 0 by rw [h2]; simp
  rw [Finset.sum_range_sub (fun x=>- cos ((2 * ↑x - 1) * π / ↑n)) n]
  rw [show (2*↑n-1)*π = 2*↑n*π-1*π by linarith]
  rw [show (2 * ↑n * π - 1 * π) / ↑n = 2*n*π/n-π/n by ring]
  rw [show 2*n*π/n=n/n*2*π by ring]
  rw [show (n:ℝ)/n=1 from div_self (show (n:ℝ)≠0 by simp; linarith)]
  simp
  rw [show -π/↑n = -(π/↑n) by ring]
  simp

lemma lemma_2 (n:ℕ) (hn:n≥2): ∑ k ∈ Finset.range n, cos (2*k*π/n) = 0 := by
  have h1 (k:ℕ) (hk:k ∈ Finset.range n) : cos (2*k*π/n) = 1/(2*sin (π/n))*(sin ((2*↑(k+1)-1)*π/n) - sin ((2*k-1)*π/n)) := by -- Using the integration and difference formula to analyze the cracking term of the general term
    have h1 : π/n∈Set.Ioo 0 π := by
      simp
      constructor
      -- 0 < π / ↑n
      simp [pi_pos]
      linarith
      -- π / ↑n < π
      nth_rw 2 [show π=π/1 by simp]
      rw [div_lt_div_iff_of_pos_left]
      simp; linarith; exact pi_pos; simp; linarith; simp
    have := sin_pos_of_mem_Ioo h1
    field_simp
    rw [sin_sub_sin]
    ring_nf
  rw [Finset.sum_congr rfl h1]
  rw [←Finset.mul_sum (Finset.range n) (fun x => sin ((2 * ↑(x + 1) - 1) * π / ↑n) - sin ((2 * ↑x - 1) * π / ↑n)) (1 / (2 * sin (π / ↑n)))]
  suffices h2 : ∑ i ∈ Finset.range n,(sin ((2 * ↑(i + 1) - 1) * π / ↑n) - sin ((2 * ↑i - 1) * π / ↑n)) = 0 by rw [h2]; simp
  rw [Finset.sum_range_sub (fun x=>sin ((2 * ↑x - 1) * π / ↑n)) n]
  rw [show (2*↑n-1)*π = 2*↑n*π-1*π by linarith]
  rw [show (2 * ↑n * π - 1 * π) / ↑n = 2*n*π/n-π/n by ring]
  rw [show 2*n*π/n=n/n*2*π by ring]
  rw [show (n:ℝ)/n=1 from div_self (show (n:ℝ)≠0 by simp; linarith)]
  simp
  rw [show -π/↑n = -(π/↑n) by ring]
  simp

theorem algebra_271509 (m n:ℕ) (hm : m > 0) (hn : n > 0) : ∑ k ∈ Finset.range m, cos (2*k*π/m) + ∑ k ∈ Finset.range n, sin (2*k*π/n) ∈ ( {0, 1} : Set ℝ ) := by
  have hm : m ≥ 1 := by linarith [hm]
  if h : m = 1 then
    rw [h, lemma_1 n hn]
    simp
  else
    have : m ≥ 2 := by
      simp [le_iff_eq_or_lt] at hm
      match hm with
      | Or.inl hh =>
        have := hh.symm
        contradiction
      | Or.inr hh =>
        exact hh
    rw [lemma_1 n hn, lemma_2 m this]
    simp
