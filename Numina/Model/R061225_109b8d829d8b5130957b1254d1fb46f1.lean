import Mathlib

theorem algebra_195843 (vA vB : ℝ) (hV : vA > 0 ∧ vB > 0)
    (h : vA * (vB + 5) = vB * (vA - 10)) (hB : vB = (2 / 3) * vA) :
    vA = 18 := by
        -- 将vB = (2/3) * vA代入方程
        rw [hB] at h 
        -- 化简代数方程
        nlinarith