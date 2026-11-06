import Mathlib

/- What is the remainder when $225^{66}-327^{66}$ is divided by $17$? -/

theorem number_theory_19457 : (225 ^66 - 327^66) % (17:ℤ) = 0 := by
  have h1: 225^66 ≡ 4^66 [ZMOD 17] := Int.ModEq.pow 66 (by unfold Int.ModEq; simp)
  have h2: 4^66 ≡ 327^66 [ZMOD 17] := Int.ModEq.pow 66 (by unfold Int.ModEq; simp)
  have h3: 225^66 ≡ 327^66 [ZMOD 17] := Int.ModEq.trans h1 h2
  have h4: 225^66 - 327^66 ≡ 0 [ZMOD 17] := Int.ModEq.sub_right (327^66) h3
  unfold Int.ModEq at h4
  exact h4
