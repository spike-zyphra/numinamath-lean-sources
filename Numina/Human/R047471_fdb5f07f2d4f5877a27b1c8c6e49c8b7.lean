import Mathlib

open Finset Filter Topology

/- 6 Let the sequence $\left\{a_{n}\right\}$ be an arithmetic sequence, and the sequence $\left\{b_{n}\right\}$ satisfies: $b_{1}=a_{1}, b_{2}=a_{2}+$ $a_{3}, b_{3}=a_{4}+a_{5}+a_{6}, \cdots$, if $\lim _{n \rightarrow \infty} \frac{b_{n}}{n^{3}}=2$, then the common difference $d$ of the sequence $\left\{a_{n}\right\}$ is
(A) $\frac{1}{2}$
(B) 1
(C) 2
(D) 4 -/
theorem algebra_273177 {a b : ℕ → ℝ} {d : ℝ}
    (ha : ∀ n, a n = a 0 + d * n)
    (hb : ∀ n, b n = ∑ i ∈ range (n + 1), a (i + n * (n + 1) / 2))
    (h : Tendsto (fun n => b n / (n + 1) ^ 3) atTop (𝓝 2)) :
    d = 4 := by
  -- Prove an auxiliary result that shows that (n * (n + 1) / 2 : ℕ) is equal
  -- to (n * (n + 1) / 2 : ℝ).
  have hn2 (n : ℕ) : (n * (n + 1) / 2 : ℕ) = (n * (n + 1) / 2 : ℝ) := by
    -- n * (n + 1) is even so n * (n + 1) = k + k for some k.
    have ⟨k, hk⟩ := Nat.even_mul_succ_self n
    -- n * (n + 1) / 2 = k.
    simp [hk, ← mul_two]
    rify at hk
    linarith
  -- Show that b(n) = (n + 1) * (a(0) - d / 2 + (d / 2) * (n + 1) ^ 2).
  have eq n : b n = (n + 1 : ℝ) * (a 0 - d / 2 + (d / 2) * (n + 1) ^ 2) := calc
    -- We have
    -- b(n) = ∑ i ∈ [0, n], (a(0) + d * i + d * (n * (n + 1) / 2))
    --      = (n + 1) * (a(0) + d * (n * (n + 1)) / 2) + d * ∑ i ∈ [0, n], i
    --      = (n + 1) * (a(0) + d * (n * (n + 1)) / 2) + d * n * (n + 1) / 2
    --      = (n + 1) * (a(0) - d / 2 + (d / 2) * (n + 1) ^ 2).
    b n = ∑ i ∈ range (n + 1), (a 0 + d * i + d * (n * (n + 1) / 2)) := by
      rw [hb]
      apply sum_congr rfl
      intro i hi
      rw [ha]
      push_cast [hn2]
      ring
    _ = (n + 1) * (a 0 + d * n * (n + 1) / 2) + d * (∑ i ∈ range (n + 1), i : ℕ) := by
      simp [sum_add_distrib, ← mul_sum]
      ring
    _ = (n + 1) * (a 0 - d / 2 + (d / 2) * (n + 1) ^ 2) := by
      rw [sum_range_id, show n + 1 - 1 = n by simp, mul_comm (n + 1), hn2]
      ring
  -- It is enough to show that lim b(n) / (n + 1)^3 = d / 2.
  suffices Tendsto (fun n => b n / (n + 1) ^ 3) atTop (𝓝 (0 + d / 2)) by
    suffices 0 + d / 2 = 2 by linarith
    -- The limit is unique so d / 2 = 2 and d = 4.
    exact tendsto_nhds_unique this h
  -- We have b(n) / (n + 1)^3 = (a(0) - d / 2) / (n + 1)^2 + d / 2.
  replace eq n : b n / (n + 1) ^ 3 = (a 0 - d / 2) / (n + 1 : ℕ) ^ 2 + d / 2 := by
    field_simp [eq]
    ring
  simp_rw [eq]
  apply Tendsto.add _ tendsto_const_nhds
  -- It is left to show that lim (a(0) - d / 2) / (n + 1)^2 = 0.
  -- We have lim (a(0) - d / 2) / (n + 1)^2 = lim (a(0) - d / 2) / n^2.
  rw [Filter.tendsto_add_atTop_iff_nat 1 (f := fun n : ℕ => (a 0 - d / 2) / n ^ 2)]
  -- lim r / n^2 = 0 for any constant r.
  exact tendsto_const_div_pow _ _ two_ne_zero