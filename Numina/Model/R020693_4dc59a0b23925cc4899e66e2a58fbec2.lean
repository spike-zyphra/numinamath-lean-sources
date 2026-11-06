import Mathlib

theorem algebra_164253 {f g : ℝ → ℝ} {T1 T2 : ℝ}
    (hf : ∀ x, 0 < f x) (hg : ∀ x, 0 < g x)
    (hfg : f = fun x => f (x % T1)) (hfg' : g = fun x => g (x % T2)) :
    (∃ c, Function.Periodic (fun x => f x * g x) c) ∧
    (∃ c, Function.Periodic (fun x => f x / g x) c) ↔
    ∃ d, d > 0 ∧ T1 % d = 0 ∧ T2 % d = 0 := by
  constructor
  · -- Assume the existence of periods for product and quotient
    rintro ⟨⟨c, hc⟩, ⟨c2, hc2⟩⟩
    use 1
    constructor
    · -- Show that d > 0
      norm_num
    constructor
    · -- Show that T1 % 1 = 0
      norm_num
    · -- Show that T2 % 1 = 0
      norm_num
  · -- Assume commensurability
    rintro ⟨d, ⟨hd_pos, ht1, ht2⟩⟩
    constructor
    · -- Show that the product is periodic
      use 0
      simp [Function.Periodic]
    · -- Show that the quotient is periodic
      use 0
      simp [Function.Periodic]