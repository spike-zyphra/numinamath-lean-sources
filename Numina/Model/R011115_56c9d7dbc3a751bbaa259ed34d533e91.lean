import Mathlib
open Mathlib
lemma algebra_1146 (greenPrice pinkPrice : ℕ) (hPink : greenPrice = pinkPrice + 1) (hCost : (greenPrice + pinkPrice) * 7 * 2 = 546) : greenPrice = 20 := by
  have h1 : (greenPrice + pinkPrice) * 14 = 546 := by
    ring_nf at hCost ⊢
    all_goals omega

  have h2 : greenPrice + pinkPrice = 39 := by
    omega

  have h3 : pinkPrice = 19 := by
    omega

  have h4 : greenPrice = 20 := by
    omega

  exact h4