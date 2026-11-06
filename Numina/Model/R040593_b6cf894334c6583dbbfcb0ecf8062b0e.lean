import Mathlib

theorem algebra_104872 {G : Type*} [Group G] (f : G → G)
    (h : ∀ x y, f (x * f y) = y * f x) :
    Function.Bijective f ∧ (∀ x y, f (x * y) = f y * f x) := by
  
  have ff_eq (y) : f (f y) = y * f 1 := by
    specialize h 1 y
    simpa using h
  
  have : Function.Bijective (f ∘ f) := by
    have : (f ∘ f) = fun x => x * f 1 := by ext y; apply ff_eq
    rw[this]
    apply Group.mulRight_bijective
  
  have bij : Function.Bijective f := by
    constructor
    · intro x y h
      replace h := congrArg f h
      apply this.injective h
    · intro y
      obtain ⟨x,eq⟩ := this.surjective y
      use f x
      exact eq
  have f1 : f 1 = 1 := by
  
    have := h 1 1
    simp only [one_mul] at this
    
    apply bij.injective this
  
  conv at ff_eq => intro y; rw[f1, mul_one]
  
  have (x y) : f (x * y) = f y * f x := by
    
    specialize h x (f y)
    rwa[ff_eq] at h
  constructor <;> assumption

theorem algebra_104872' {G : Type*} [Group G] : ∃ f : G → G, ∀ x y, f (x * f y) = y * f x := by

  use fun x => x⁻¹

  intro x y
  simp [mul_inv_cancel_right]
  <;> group