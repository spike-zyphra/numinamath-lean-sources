import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/- Let $z$ be a complex number such that $|z| = 1.$  Find the maximum value of
\[|1 + z| + |1 - z + z^2|.\] -/
theorem algebra_18771 :
  IsGreatest {x | ∃ z : ℂ, ‖z‖ = 1 ∧ x = ‖1 + z‖ + ‖1 - z + z^2‖} (13/4) := by
    constructor <;>
    simp [upperBounds]
    -- 证明一个辅助引理：(√15/8)² = 15/64
    have h1 : √15 / 8 * (√15 / 8) = 15 / 64:= by
      calc _ = (√15 / 8) ^ 2:= by ring
            _ =  √15 ^ 2 / 8 ^ 2:= by ring
            _ = 15 / 8 ^ 2:= by rw [show (√15 ^ 2 = 15) by refine sq_sqrt (by linarith)]
            _ = 15 / 64:= by norm_num
    .
      -- 构造一个复数 z = -7/8 + (√15/8)i，这是能达到最大值的点
      use { re := -7 / 8, im := √15 / 8}
      simp [Complex.abs]
      constructor
      .
        norm_num
        rw [h1]
        norm_num
      .
        -- 计算 |1 - z + z²| 的值
        simp [normSq, pow_two]
        norm_num
        rw [h1]
        ring_nf
        rw [show ((1 : ℝ) / 4 = (1 / 2) ^ 2) by norm_num]
        rw [show ((5929 : ℝ) / 1024 = (77 / 32) ^ 2) by norm_num]
        rw [show √((1 / 2) ^ 2) = 1 / 2 by refine sqrt_sq (by linarith)]
        rw [show √15 ^ 2 = 15 by refine sq_sqrt (by norm_num)]
        ring_nf
        rw [show ((121 : ℝ) / 16) = (11 / 4) ^ 2 by norm_num]
        rw [show √((11 / 4) ^ 2) = 11 / 4 by refine sqrt_sq (by linarith)]
        norm_num
    .
      -- 证明对任意满足条件的复数 z = a + bi，表达式的值不超过 13/4
      intro x z hz hx
      -- 将复数 z 表示为实部和虚部的形式
      have h1 : z = { re := z.re, im := z.im}:= by rfl
      let a:= z.re
      let b:= z.im
      have ha : a = z.re:= by rfl
      have hb : b = z.im:= by rfl
      rw [←ha, ←hb] at h1
      rw [h1] at hx
      rw [h1] at hz
      simp [Complex.abs] at hz
      simp [Complex.abs] at hx
      simp [normSq] at hx
      ring_nf at hz hx
      -- 计算 z² 的实部和虚部
      simp [pow_two] at hx
      ring_nf at hx
      -- 利用 |z| = 1 得到 b² = 1 - a²
      replace hz : b ^ 2 = 1 - a ^ 2:= by linarith
      rw [show (b ^ 4 = (b ^ 2) * (b ^ 2)) by ring_nf] at hx
      rw [hz] at hx
      ring_nf at hx
      -- 引入变量 t = √(2 + 2a) 进行变量替换
      let t:= √(2 + a * 2)
      have ht : t = √(2 + a * 2):= by rfl
      -- 证明 a 的取值范围：-1 ≤ a ≤ 1
      have h2 : b ^ 2 ≥ 0:= by exact sq_nonneg b
      rw [hz] at h2
      have h3 : a ≥ - 1:= by
        by_contra!
        have h4 : a ^ 2 > 1:= by nlinarith only [this]
        linarith
      have ht2 : t ^ 2 = 2 + a * 2:= by
        rw [ht]
        have h5 : 2 + a * 2 ≥ 0:= by linarith
        exact sq_sqrt h5
      replace ht2 : a = t ^ 2 / 2 - 1:= by linarith
      rw [←ht, ht2] at hx
      ring_nf at hx
      -- 化简表达式
      rw [show (9 - t ^ 2 * 6 + t ^ 4 = (3 - t ^ 2) ^ 2) by ring_nf] at hx
      rw [show √((3 - t ^ 2) ^ 2) = |3 - t ^ 2| by exact sqrt_sq_eq_abs (3 - t ^ 2)] at hx
      -- 证明 t 的取值范围：0 ≤ t ≤ 2
      have g1 : t ≥ 0:= by
        rw [ht]
        exact sqrt_nonneg (2 + a * 2)
      have h4 : a ≤ 1:= by
        by_contra!
        have h4 : a ^ 2 > 1:= by nlinarith only [this]
        linarith
      have h5 : 2 + a * 2 ≤ 4:= by linarith
      have g2 : t ≤ 2:= by
        rw [ht]
        calc _ ≤ √4:= by exact sqrt_le_sqrt h5
             _ = √(2 ^ 2):= by norm_num
             _ = 2:= by refine sqrt_sq (by linarith)
      clear h2 h3 h4 h5
      -- 分类讨论：t ≤ √3 或 t > √3
      have g3 : t ≤ √3 ∨ t > √3:= by exact le_or_lt t √3
      rcases g3 with g3 | g3
      .
        -- 当 t ≤ √3 时
        have h2 : t ^ 2 ≤ √3 ^ 2:= by exact pow_le_pow_left₀  g1 g3 2
        rw [show √3 ^ 2 = 3 by refine sq_sqrt (by linarith)] at h2
        replace h2 : 3 - t ^ 2 ≥ 0:= by linarith
        have h3 : |3 - t ^ 2| = 3 - t ^ 2:= by exact _root_.abs_of_nonneg h2
        rw [h3] at hx
        have h4 : (t + (3 - t ^ 2)) = 13 / 4 - (t - 1 / 2) ^ 2:= by ring_nf
        rw [h4] at hx
        have h5 : (t - 1 / 2) ^ 2 ≥ 0:= by exact sq_nonneg (t - 1 / 2)
        linarith
      .
        -- 当 t > √3 时
        have h2 : √3 > 0:= by refine sqrt_pos_of_pos (by linarith)
        have h3 : t ^ 2 > √3 ^ 2:= by nlinarith only [g3, h2]
        rw [show √3 ^ 2 = 3 by refine sq_sqrt (by linarith)] at h3
        replace h3 : 3 - t ^ 2 < 0:= by linarith
        have h4 : |3 - t ^ 2| = -(3 - t ^ 2):= by exact abs_of_neg h3
        rw [h4] at hx
        simp at hx
        have h5 : t ^ 2 ≤ 4:= by nlinarith only [g1, g2]
        linarith
