import Mathlib
open Real

theorem inequalities_3962 (a b c : ℝ) (h₀ : a + b + c = 0) (h₁ : abs a + abs b + abs c = 1) :
    a + b / 2 + c / 3 ≤ 1 / 3 := by 
  have hc : c = -a - b := by linarith
  rw [hc] at h₁
  have h2 : a + b / 2 + c / 3 = 2 * a / 3 + b / 6 := by
    rw [hc]
    linarith
  rw [h2]
  cases' abs_cases a with ha ha
  · cases' abs_cases b with hb hb
    · cases' abs_cases (-a - b) with hc1 hc1
      · -- Case $a \geq 0$, $b \geq 0$, $-a - b \geq 0$
        nlinarith
      · -- Case $a \geq 0$, $b \geq 0$, $-a - b < 0$
        nlinarith
    · cases' abs_cases (-a - b) with hc1 hc1
      · -- Case $a \geq 0$, $b < 0$, $-a - b \geq 0$
        nlinarith
      · -- Case $a \geq 0$, $b < 0$, $-a - b < 0$
        nlinarith
  · cases' abs_cases b with hb hb
    · cases' abs_cases (-a - b) with hc1 hc1
      · -- Case $a < 0$, $b \geq 0$, $-a - b \geq 0$
        nlinarith
      · -- Case $a < 0$, $b \geq 0$, $-a - b < 0$
        nlinarith
    · cases' abs_cases (-a - b) with hc1 hc1
      · -- Case $a < 0$, $b < 0$, $-a - b \geq 0$
        nlinarith
      · -- Case $a < 0$, $b < 0$, $-a - b < 0$
        nlinarith