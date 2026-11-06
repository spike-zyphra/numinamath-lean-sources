import Mathlib

theorem algebra_22550 {f : ℕ → ℤ} (hf : ∀ n, f n = match n with
    | 0 => 211
    | 1 => 375
    | 2 => 420
    | 3 => 523
    | n + 4 => f (n + 3) - f (n + 2) + f (n + 1) - f n
  ) : f 530 + f 752 + f 974 = 898 := by
  set_option maxRecDepth 20000 in
  norm_num [hf]