import Mathlib

/-- Let (G,.) be a group and $f: G \rightarrow G$ a function with the property:
  $f(x \cdot f(y))=y \cdot f(x), \forall x, y \in G$.
a) Show that $\mathrm{f}$ is bijective and that $f(x \cdot y)=f(y) \cdot f(x), \forall x, y \in G$.
b) Provide an example of a function $\mathrm{f}$ that satisfies the property stated in the problem. -/
theorem algebra_104872 {G : Type*} [Group G] (f : G → G)
    (h : ∀ x y, f (x * f y) = y * f x) :
    Function.Bijective f ∧ (∀ x y, f (x * y) = f y * f x) := by
  -- By assumption $f(f(y)) = f(1f(y)) = y f(1)$ forall $y \in G$.
  have ff_eq (y) : f (f y) = y * f 1 := by
    specialize h 1 y
    simpa using h
  -- Since multiplication with a fixed element is bijective, so is $f \circ f$.
  have : Function.Bijective (f ∘ f) := by
    have : (f ∘ f) = fun x => x * f 1 := by ext y; apply ff_eq
    rw[this]
    apply Group.mulRight_bijective
  -- Hence, $f$ is also bijective.
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
  -- From the assumption, we get $f(f(1)) = f(1 f(1)) = 1 f(1) = f(1)$.
    have := h 1 1
    simp only [one_mul] at this
    -- Injectivity implies $f(1) = 1$.
    apply bij.injective this
  -- Therefore, $f(f(y)) = y$.
  conv at ff_eq => intro y; rw[f1, mul_one]
  -- Use the assumption to obtain $f(xf(f(y))) = f(y) f(x)$,
  have (x y) : f (x * y) = f y * f x := by
    -- such that from the previous result $f(xy) = f(y) f(x)$, as desired.
    specialize h x (f y)
    rwa[ff_eq] at h
  constructor <;> assumption

-- The inversion function $x \mapsto x^{-1}$ is an explicit example for such a function, as $(x y^{-1})^{-1} = y x^{-1}$.
theorem algebra_104872' {G : Type*} [Group G] : ∃ f : G → G, ∀ x y, f (x * f y) = y * f x := by
  exists fun x => x⁻¹
  intro x y
  simp