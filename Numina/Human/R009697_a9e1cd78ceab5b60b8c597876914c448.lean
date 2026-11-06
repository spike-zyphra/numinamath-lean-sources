import Mathlib
/-Kimberly borrows $1000$ dollars from Lucy, who charged interest of $5\%$ per month (which compounds monthly). What is the least integer number of months after which Kimberly will owe more than twice as much as she borrowed?-/

theorem algebra_822 (P : ℕ → ℝ) (hP : ∀ n, P n = 1000 * (1 + 0.05) ^ n) :
    IsLeast {n | P n > 2000} 15 := by
    -- unfold
    dsimp[IsLeast]
    -- both side
    constructor
    -- use hP
    have h15:= hP 15
    rw [h15]
    norm_num
    -- the other side
    simp [lowerBounds] 
    -- prove by contra
    intro n hn
    -- prove mono
    have h1: (1:ℝ) < (1+5e-2):= by norm_num
    have hmono:= pow_right_strictMono h1
    -- use mono
    by_contra hx
    push_neg at hx
    -- consider n<16
    by_cases h14: n<14
    have := hmono h14
    simp at this
    -- now we need to find contra
    have hn1:= hP n
    rw [hn1] at hn
    -- simp at hn
    have h2000:(2000:ℝ) = 1000 * 2:= by norm_num
    rw [h2000] at hn
    simp at hn
    -- now use 15
    have ht:= lt_trans hn this
    norm_num at ht
    -- consider n = 14
    have h14: n = 14 := by omega
    rw [h14] at hn
    have h14p:=hP 14
    -- calculate 14
    rw [h14p] at hn
    norm_num at hn




