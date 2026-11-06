import Mathlib

theorem my_favorite_theorem_prop_is_abelian
  {G : Type u_1}
  [inst_grp : Group G] [inst_fin : Fintype G]
  (f : G ≃* G)
  (hf_involution : ⇑f ∘ ⇑f = id)
  (hf_fixed_point : ∀ (x : G), f x = x → x = 1) :
  ∀ (a b : G), a * b = b * a := by
  intros a b
  have h_fx_is_inv : ∀ x : G, f x = x⁻¹ := by
    intro x
    let φ : G → G := fun y => y⁻¹ * f y
    have hφ_inj : Function.Injective φ := by
      intro a b hab_φ
      simp only [φ] at hab_φ
      suffices a * b⁻¹ = 1 by
        rwa [mul_inv_eq_one] at this
      apply hf_fixed_point (a * b⁻¹)
      calc f (a * b⁻¹)
          = f a * f (b⁻¹)         := by exact map_mul f a b⁻¹
        _ = f a * (f b)⁻¹         := by rw [MulEquiv.map_inv f b]
        _ = (a * (b⁻¹ * f b)) * (f b)⁻¹ := by rw [← mul_left_inj a⁻¹, ← hab_φ, mul_inv_cancel_left]
        _ = a * b⁻¹ * (f b * (f b)⁻¹) := by simp only [mul_assoc]
        _ = a * b⁻¹ * 1                := by rw [mul_inv_cancel (f b)]
        _ = a * b⁻¹                    := by rw [mul_one (a * b⁻¹)]

    have hφ_surj : Function.Surjective φ := by
      apply Function.Injective.surjective_of_fintype
      exact f.toEquiv
      apply hφ_inj
    obtain ⟨y, hy⟩ : ∃ y, φ y = x := hφ_surj x
    have hf_apply_f_apply (z : G) : f (f z) = z := by
      exact congr_fun hf_involution z
    calc f x
        = f (y⁻¹ * f y)            := by rw [← hy]
      _ = f (y⁻¹) * f (f y)       := map_mul f y⁻¹ (f y)
      _ = (f y)⁻¹ * f (f y)       := by rw [MulEquiv.map_inv f y]
      _ = (f y)⁻¹ * y             := by rw [hf_apply_f_apply y]
      _ = (f y)⁻¹ * (y⁻¹)⁻¹       := by rw [inv_inv y]
      _ = (y⁻¹ * f y)⁻¹           := by rw [←mul_inv_rev y⁻¹ (f y)]
      _ = x⁻¹                     := by unfold φ at hy;rw [hy]

  calc
    a * b = ( (a * b)⁻¹ )⁻¹                    := by rw [inv_inv]
        _ = ( f (a * b) )⁻¹                    := by rw [h_fx_is_inv (a * b)]
        _ = ( f a * f b )⁻¹                    := by rw [map_mul]
        _ = ( a⁻¹ * b⁻¹ )⁻¹                    := by rw [h_fx_is_inv a, h_fx_is_inv b]
        _ = (b⁻¹)⁻¹ * (a⁻¹)⁻¹                  := by rw [mul_inv_rev]
        _ = b * a                              := by simp only [inv_inv]