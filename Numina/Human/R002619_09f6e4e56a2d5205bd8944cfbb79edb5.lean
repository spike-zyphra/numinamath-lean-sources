import Mathlib



/- How many ordered pairs of real numbers (x,y) satisfy the following system of equations?
\begin{align*} x+3y&=3 \ \big||x|-|y|\big|&=1 \end{align*}
(A) 1
(B) 2
(C) 3
(D) 4
(E) 8
 -/
theorem algebra_96627 :
{(x, y) : ℝ × ℝ | x + 3 * y = 3 ∧ |abs x - abs y| = 1}.ncard = 3 := by
  -- lemmas needed later
  have h : |(1:ℝ)/2| = (1:ℝ)/2 := by norm_num
  have h' : |(3:ℝ)/2| = (3:ℝ)/2 := by norm_num
  -- we'll prove solutin set is (-3, 2), (0, 1), (3/2, 1/2)
  have : {(x, y) : ℝ × ℝ | x + 3 * y = 3 ∧ |abs x - abs y| = 1} = {(-3, 2), (0, 1), (3/2, 1/2)} := by
    ext ⟨x, y⟩
    constructor
    -- if (x, y) solution then do case work on |x|-|y|, |x|, |y|. many branches are impossible, only 3 branch remain, which can be solved by linear arithmetic
    . intro ⟨h₁, h₂⟩
      obtain h | h := le_or_lt 0 (abs x-abs y)
      all_goals first|(rw [abs_of_neg h] at h₂)|(rw [abs_of_nonneg h] at h₂)
      all_goals (
        obtain h | h := le_or_lt 0 x
        all_goals first|(rw [abs_of_neg h] at h₂)|(rw [abs_of_nonneg h] at h₂)
        all_goals (
          obtain h | h := le_or_lt 0 y
          all_goals first|(rw [abs_of_neg h] at h₂)|(rw [abs_of_nonneg h] at h₂)
          all_goals simp only [Set.mem_insert_iff, Prod.mk.injEq, Set.mem_singleton_iff]
          any_goals linarith
        )
      )
      any_goals left;constructor <;> linarith
      all_goals first|right;left;constructor <;> linarith|right;right;constructor <;> linarith
    -- if (x, y) is from those 3 values, just plug in and compute
    . intro h
      obtain h | h | h := h
      all_goals constructor
      all_goals obtain ⟨rfl, rfl⟩ := h
      all_goals norm_num
      rw [h, h']; norm_num
  -- finally prove the fact that 3 solution are distinct so set size 3
  rw [this]
  set a :ℝ×ℝ := (-3, 2) with ha
  set b :ℝ×ℝ := (0, 1) with hb
  set c :ℝ×ℝ := (3/2, 1/2) with hc
  have hab: a ≠ b := by rw [ha, hb]; norm_num
  have hbc: b ≠ c := by rw [hc, hb]; norm_num
  have hac: a ≠ c := by rw [hc, ha]; norm_num
  simp [hab, hbc, hac]