import Mathlib

open Topology Filter Real Finset

/- Problem 1. Let $a_{0}, a_{1}, \ldots, a_{k}(k \geq 1)$ be real numbers such that $a_{0}+a_{1}+\ldots+a_{k}=0$. Calculate $\lim _{n \rightarrow \infty}\left(a_{0} \sqrt[3]{n}+a_{1} \sqrt[3]{n+1}+\ldots+a_{k} \sqrt[3]{n+k}\right)$. -/
theorem calculus_120121 (k : ℕ) (hk : k ≥ 1) (a : ℕ → ℝ)
    (h₀ : ∑ i in range (k + 1), a i = 0) :
    Tendsto (λ n : ℕ => ∑ i in range (k + 1), a i * (n + i) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
  -- Let f(i, n) = (n + i)^(1/3) - n^(1/3).
  set f : ℕ → ℕ → ℝ := fun i n => (n + i) ^ (1 / 3 : ℝ) - n ^ (1 / 3 : ℝ)
  -- Show that ∑ i ∈ [0, k], a(i) * (n + i)^(1/3) = ∑ i ∈ [1, k], a(i) * f(i, n).
  have heq (n : ℕ) : ∑ i ∈ range (k + 1), a i * (n + i) ^ (1 / 3 : ℝ) = ∑ i ∈ Icc 1 k, a i * f i n := calc
    -- We have ∑ i ∈ [0, k], a(i) * (n + i)^(1/3) = a(0) * n^(1/3) + ∑ i ∈ [1, k], a(i) * (n + i)^(1/3).
    _ = a 0 * n ^ (1 / 3 : ℝ) + ∑ i ∈ Ico 1 (k + 1), a i * (n + i) ^ (1 / 3 : ℝ) := by
        rw [sum_range_eq_add_Ico _ (by omega)]
        simp only [CharP.cast_eq_zero, add_zero]
    -- From h₀ we get that a(0) = -∑ i ∈ [1, k], a(i).
    _ = (-∑ i ∈ Ico 1 (k + 1), a i) * n ^ (1 / 3 : ℝ) + ∑ i ∈ Ico 1 (k + 1), a i * (n + i) ^ (1 / 3 : ℝ) := by
        congr
        rw [sum_range_eq_add_Ico _ (by omega)] at h₀
        linarith
    -- We get (-∑ i ∈ [1, k], a(i)) * n^(1/3) + ∑ i ∈ [1, k], a(i) * (n + i)^(1/3)
    --      = ∑ i ∈ [1, k], a(i) * ((n + i)^(1/3) - n^(1/3))
    --      = ∑ i ∈ [1, k], a(i) * f(i, n).
    _ = ∑ i ∈ Icc 1 k, a i * f i n := by
        rw [← sum_neg_distrib, sum_mul, ← sum_add_distrib]
        apply sum_congr rfl
        intro i hi
        ring
  simp_rw [heq]
  -- It is enough to show that for all i, lim f(i, n) = 0 as n tends to infinity.
  suffices ∀ i ∈ Icc 1 k, Tendsto (f i) atTop (𝓝 0) by
    rw [show (0 : ℝ) = ∑ i ∈ Icc 1 k, a i * 0 by simp]
    apply tendsto_finset_sum
    intro i hi
    apply Tendsto.const_mul
    exact this i hi
  intro i hi
  rw [NormedAddCommGroup.tendsto_atTop']
  -- Show that for any 0 < e, there exists N such that |f(i, n)| < e for all n > N.
  intro e he
  -- Let N be such that (i / e)^3 ≤ N.
  have ⟨N, hN⟩ := exists_nat_ge ((i / e) ^ 3)
  use N
  intro n hn
  have hn_pos : 0 < n := by omega
  have hni_pos : 0 < n + i := by omega
  -- Show that f(i, n) = i / (((n + i)^2)^(1/3) + ((n + i) * n)^(1/3) + (n^2)^(1/3)).
  have hf : f i n = i / (((n + i)^2) ^ (1 / 3 : ℝ) + ((n + i) * n) ^ (1 / 3 : ℝ) + (n ^ 2) ^ (1 / 3 : ℝ)) := by
    dsimp [f]
    -- We have a - b = (a ^ 3 - b ^ 3) / (a ^ 2 + a * b + b ^ 2) for any positivite a and b.
    have heq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : a - b = (a ^ 3 - b ^ 3) / (a ^ 2 + a * b + b ^ 2) := by
      field_simp; ring
    -- Take a = (n + i)^(1/3) and b = n^(1/3) and get the result after algebraic simplifications.
    rw [heq (by positivity) (by positivity)]
    congrm ?_ / (?_ + ?_ + ?_)
    · have h3 {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
        norm_num
      rw [h3 (by positivity), h3 (by positivity)]
      ring
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm]
    · rw [Real.mul_rpow (by positivity) (by positivity)]
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm]
  simp only [sub_zero, norm_eq_abs, hf]
  -- 0 ≤ f(i, n) so |f(i, n)| = f(i, n).
  rw [abs_of_nonneg (by positivity), ← hf]
  simp only [mem_Icc] at hi
  have hi_pos : 0 < i := by omega
  -- Show that f(i, n) < e.
  calc
    -- We have f(i, n) = i / (((n + i)^2)^(1/3) + ((n + i) * n)^(1/3) + (n^2)^(1/3))
    --                 ≤ i / (n^2)^(1/3) (because ((n + i)^2)^(1/3) + ((n + i) * n)^(1/3) + (n^2)^(1/3) ≥ (n^2)^(1/3)).
    f i n ≤ i / (n ^ 2) ^ (1 / 3 : ℝ) := by
        rw [hf]
        gcongr
        simp only [le_add_iff_nonneg_left]
        positivity
    -- i / (n^2)^(1/3) ≤ i / n^(1/3) (because n^2 ≥ n).
    _ ≤ i / n ^ (1 / 3 : ℝ) := by
        gcongr
        norm_cast
        apply Nat.le_self_pow (by norm_num)
    -- i / n^(1/3) < i / ((i / e)^3)^(1/3) (because n > N ≥ (i / e)^3).
    _ < i / ((i / e) ^ 3) ^ (1 / 3 : ℝ) := by
        gcongr
        rify at hn
        linarith
    -- i / ((i / e)^3)^(1/3) = i / (i / e) = e.
    -- We conclude that f(i, n) < e.
    _ = e := by
        field_simp
        rw [← div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
        field_simp