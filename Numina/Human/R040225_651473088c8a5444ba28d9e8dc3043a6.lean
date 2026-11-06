import Mathlib

/- Define an odd function $f(x)$ on $\mathbb{R}$, such that for $\forall x \in \mathbb{R}$, it holds that $f\left( \dfrac {3}{2}+x\right)=f\left( \dfrac {3}{2}-x\right)$, and it satisfies $f(5) > -2$, $f(2)=m- \dfrac {3}{m}$. The range of the real number $m$ is \_\_\_\_\_\_. -/
theorem algebra_9416 {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) (h : ∀ x, f (3 / 2 + x) = f (3 / 2 - x))
    (h5 : f 5 > -2) (m : ℝ) (mne0 : m ≠ 0) (hm : f 2 = m - 3 / m) :
    m < -1 ∨ 0 < m ∧ m < 3 := by

  -- f 5 = f (-2) = -f 2
  have h1 : f 5 = -f 2 := by
    calc f 5 = f (3 / 2 + 7 / 2) := by norm_num
         _ = f (3 / 2 - 7 / 2) := by rw [h]
         _ = f (-2) := by norm_num
         _ = -f 2 := by rw [hf]

  -- Clear everything about f
  replace hm : m - 3 / m < 2 := by linarith
  clear f hf h h5 h1

  -- Case analysis on m < 0 ∨ m = 0 ∨ 0 < m
  obtain h | h | h := lt_trichotomy m 0
  . -- If m < 0, then (m - 3 / m) * m > 2 * m, and we can derive that m < -1
    left
    replace hm : (m - 3 / m) * m > 2 * m := by nlinarith
    field_simp [mne0] at hm
    replace hm : (m + 1) * (m - 3) > 0 := by linarith
    have : m - 3 < 0 := by linarith
    nlinarith

  . -- m cannot be 0
    exfalso
    exact mne0 h

  . -- If 0 < m, then (m - 3 / m) * m < 2 * m, and we can derive that 0 < m < 3
    refine Or.inr ⟨h, ?_⟩
    replace hm : (m - 3 / m) * m < 2 * m := by nlinarith
    field_simp [mne0] at hm
    replace hm : (m + 1) * (m - 3) < 0 := by linarith
    have : m + 1 > 0 := by linarith
    nlinarith
