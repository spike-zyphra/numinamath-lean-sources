import Mathlib
open Mathlib
theorem algebra_97709 (x : ℕ → ℤ)
(h0 : x 0 = 211)
(h1 : x 1 = 375)
(h2 : x 2 = 420)
(h3 : x 3 = 523)
(h4 : ∀ n, x (n + 4) = x (n + 3) - x (n + 2) + x (n + 1) - x n) :
x 530 + x 752 + x 974 = 898 := by

  set_option maxRecDepth 10000 in 
  norm_num [h0, h1, h2, h3, h4]