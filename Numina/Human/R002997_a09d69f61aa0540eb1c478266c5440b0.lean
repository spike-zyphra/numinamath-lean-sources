import Mathlib

/- 5. Given distinct complex numbers $m, n$ satisfying $m n \neq 0$, the set $\left\{m^{2}, n^{2}\right\}=\{m, n\}$, then $m+n=$

 untranslated portion:
将上面的文本翻译成英文，请保留源文本的换行和格式，直接输出翻译结果。

Note: The last sentence is a note about the translation request and is not part of the text to be translated. Here is the translation with the note removed:

5. Given distinct complex numbers $m, n$ satisfying $m n \neq 0$, the set $\left\{m^{2}, n^{2}\right\}=\{m, n\}$, then $m+n=$ -/
theorem algebra_141373 (m n : ℂ) (h₁ : m ≠ n) (h₂ : m * n ≠ 0) (h : ({m, n} : Set _) = {m ^ 2, n ^ 2}) : m + n = -1 := by
  -- We get `m ≠ 0` and `n ≠ 0` from `h₂`
  replace ⟨h₂, h₃⟩ := mul_ne_zero_iff.mp h₂
  -- We have `m = m ^ 2` and `n = n ^ 2` or `m = n ^ 2` and `n = m ^ 2`
  rw [Set.pair_eq_pair_iff] at h
  -- Case analysis on the two possible equalities
  rcases h with ⟨h₄, h₅⟩ | ⟨h₄, h₅⟩
  . -- If `m = m ^ 2` and `n = n ^ 2`, then `m = 0` or `m = 1`, and `n = 0` or `n = 1`
    -- But it contradicts to `m ≠ 0`, `n ≠ 0` and `m ≠ n`
    replace h₄ : m * (m - 1) = 0 := by linear_combination -h₄
    replace h₅ : n * (n - 1) = 0 := by linear_combination -h₅
    simp [sub_eq_zero, h₂, h₃] at h₄ h₅
    simp [h₄, ← h₅] at h₁
  . -- If `m = n ^ 2` and `n = m ^ 2`
    -- We subtract the two equations and get `(m - n) * (m + n + 1) = 0`
    -- So `m + n = -1`.
    have h₆ : (m - n) * (m + n - (-1)) = 0 := by linear_combination h₄ - h₅
    simp [-sub_neg_eq_add, sub_eq_zero] at h₆
    simpa [h₁] using h₆
