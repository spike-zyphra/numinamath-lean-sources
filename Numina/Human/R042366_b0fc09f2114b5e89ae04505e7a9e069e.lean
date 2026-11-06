import Mathlib

/- A fruit salad consists of blueberries, raspberries, grapes, and cherries.  The fruit salad has a total of 280 pieces of fruit.  There are twice as many raspberries as blueberries, three times as many grapes as cherries, and four times as many cherries as raspberries.  How many cherries are there in the fruit salad?
(A) 8(B) 16(C) 25(D) 64(E) 96 -/
theorem algebra_95201 (blueberry raspberry grape cherry : ℕ)
(h₀ : blueberry + raspberry + grape + cherry = 280)
(h₁ : raspberry = 2 * blueberry)
(h₂ : grape = 3 * cherry)
(h₃ : cherry = 4 * raspberry) :
cherry = 64 := by
    rify at h₀ h₁ h₂ h₃
    rify
    --find any other fruit in terms of bluebarry
    rw[h₁] at h₃
    rw[h₃] at h₂
    --find how many bluebarries are there in the salad
    rw[h₁,h₂,h₃] at h₀
    ring_nf at h₀ 
    have hk := congrFun (congrArg HMul.hMul h₀) (1/35)
    norm_num at hk
    simp at hk
    --find how many cherry there are
    rw[hk] at h₃
    ring_nf at h₃
    exact h₃