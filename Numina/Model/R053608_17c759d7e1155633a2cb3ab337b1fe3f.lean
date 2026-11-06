import Mathlib

theorem algebra_244084 (total_inhabitants : ℕ) (h : total_inhabitants = 29970)
    (men_only_sports : ℕ) (women_only_sports : ℕ)
    (h1 : men_only_sports = total_inhabitants * (2 / 9 : ℚ))
    (h2 : women_only_sports = total_inhabitants * (2 / 15 : ℚ))
    (h3 : total_inhabitants - men_only_sports - women_only_sports = 5 * (men_only_sports + women_only_sports)) :
    total_inhabitants = 29970 := by 
        exact h