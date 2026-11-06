import Mathlib

/- 162. $7^{x}-3 \cdot 7^{x-1}+7^{x+1}=371$.

Translate the above text into English, keeping the original text's line breaks and format, and output the translation result directly.

162. $7^{x}-3 \cdot 7^{x-1}+7^{x+1}=371$. -/
theorem algebra_153485 (x : ℕ) (h : 7^x - 3 * 7^(x - 1) + 7^(x + 1) = 371) : x = 2 := by
  have hx1 : x = 2 := by
    cases' x with x
    · -- x = 0
      exfalso
      norm_num at h
    · cases' x with x
      · -- x = 1, but equation is false
        exfalso
        norm_num at h
      · cases' x with x
        · -- x = 2, verify equation
          norm_num at h
          all_goals omega
        · -- x ≥ 3, but equation is false
          all_goals omega
  exact hx1