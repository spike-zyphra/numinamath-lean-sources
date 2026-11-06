import Mathlib

open Real Matrix

/- ## Subject I. (40 points)

Let $G=\left\{A_{x} / x \in \mathbb{R}\right\}, A_{x}=\left(\begin{array}{ccc}1 & 0 & x \\ -x & 1 & -\frac{1}{2} x^{2} \\ 0 & 0 & 1\end{array}\right)$.

a) Show that $(G, \cdot)$ is an abelian group;

b) Prove that $(G, \cdot)$ is isomorphic to $(\mathbb{R}, +)$;

c) Calculate $A^{2015}, A \in G$.

Prof. Anca Cristina Hodorogea, ISJ Cluj -/
theorem algebra_106682 {G : Set (Matrix (Fin 3) (Fin 3) ℝ)}
    (hG : G = {A | ∃ x : ℝ, A = !![1, 0, x; -x, 1, -1/2 * x^2; 0, 0, 1]}) :
    1 ∈ G ∧ (∀ A ∈ G, A⁻¹ ∈ G) ∧ (∀ A ∈ G, ∀ B ∈ G, A * B ∈ G ∧ A * B = B * A) ∧
    (∃ f : Matrix (Fin 3) (Fin 3) ℝ → ℝ, Set.BijOn f G Set.univ ∧ ∀ A ∈ G, ∀ B ∈ G, f (A * B) = f (A) + f (B)) ∧
    ∀ A ∈ G, A ^ 2015 = !![1, 0, 2015 * A 0 2; -2015 * A 0 2, 1, -1/2*(2015 * A 0 2)^2; 0, 0, 1] := by
  -- Let g be defined as follows:
  -- g(x) = [1, 0, x; -x, 1, -1/2 * x^2; 0, 0, 1].
  set g : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun x => !![1, 0, x; -x, 1, -1/2 * x^2; 0, 0, 1]
  -- Show that g(x + y) = g(x) * g(y).
  have g_add x y : g (x + y) = g x * g y := by
    -- The result follows from the definition of matrix multiplication.
    simp [g]
    ring_nf
  -- Show that g(0) = 1 (the identity matrix).
  have g_one : g 0 = 1 := by
    simp [g]
    exact Matrix.one_fin_three.symm
  -- Show that g(x) ∈ G for all x.
  have gG x : g x ∈ G := by
    simp only [hG, Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq, g]
    use x
  -- For all A ∈ G we have A = g(A 0 2).
  have g_ex {A} (hA : A ∈ G) : A = g (A 0 2) := by
    simp only [hG, Set.mem_setOf_eq] at hA
    replace ⟨x, hA⟩ := hA
    simp [hA]
  constructorm* _ ∧ _
  -- Prove that 1 ∈ G. We have 1 = g(0) ∈ G.
  · simp only [← g_one, gG 0]
  -- Prove that for all A ∈ G, A⁻¹ ∈ G.
  · intro A hA
    -- It is enough to show that A⁻¹ = g(-A 0 2) since g(x) ∈ G for all x.
    suffices A⁻¹ = g (-A 0 2) by simp only [this, Fin.isValue, gG]
    -- Show that A * g(-A 0 2) = 1.
    apply inv_eq_right_inv
    -- We have A * g(-A 0 2) = g(A 0 2) * g(-A 0 2) = g(A 0 2 - A 0 2) = g(0) = 1.
    nth_rw 1 [g_ex hA, ← g_add, add_neg_cancel, g_one]
  · intro A hA B hB
    -- Show that for all A ∈ G, B ∈ G, A * B ∈ G and A * B = B * A.
    -- We have A = g(A 0 2), B = g(B 0 2).
    -- So A * B = g(A 0 2 + B 0 2) = g(B 0 2 + A 0 2) = B * A.
    -- Moreover g(x) ∈ G for all x.
    rw [g_ex hA, g_ex hB]
    simp_rw [← g_add, gG, add_comm, and_true]
  -- Show that G and (ℝ, +) are isomorphic.
  -- Define f from 3 x 3 matrices to ℝ as f(A) = A 0 2.
  · use fun A => A 0 2
    constructorm* _ ∧ _
    -- Show that f is bijective on G.
    · simp [Set.BijOn, Set.MapsTo]
      constructor
      -- Show that f is injective on G.
      -- It is enough to show that f has a left inverse on G.
      -- Demonstrate that g is a left inverse of f on G.
      · apply Set.LeftInvOn.injOn (f₁' := g)
        simp [Set.LeftInvOn]
        -- We need to show that g(A 0 2) = A for A ∈ G.
        -- It follows from the definitions of g and G.
        intro A hA
        simp [g, hG] at hA ⊢
        have ⟨x, hx⟩ := hA
        simp [hx]
      -- Show that f is surjective on G.
      -- It is enough to show that f has a right inverse on G.
      -- Demonstrate that g is a right inverse of f on G.
      · apply Set.RightInvOn.surjOn (f' := g)
        -- We need to show that g(x) 0 2 = x for all x ∈ ℝ.
        -- This follows from the definition of g.
        · simp [Set.RightInvOn, Set.LeftInvOn, g]
        · simp [gG]
    -- Show that f(A * B) = f(A) + f(B).
    · intro A hA B hB
      -- We have f(A * B) = (A * B) 0 2 = (g(A 0 2) * g(B 0 2)) 0 2
      --             = g(A 0 2 + B 0 2) 0 2 = A 0 2 + B 0 2 = f(A) + f(B).
      nth_rw 1 [g_ex hA, g_ex hB, ← g_add]
      simp [g]
  · intro A hA
    -- Let A ∈ G and find A^2015.
    nth_rw 1 [g_ex hA]
    -- Show that g(x)^n = g(n * x) for all x and n.
    have g_pow (x : ℝ) (n : ℕ) : g x ^ n = g (n * x) := by
      -- Proof by induction.
      induction n with
      -- If n = 0 then 1 = g(x)^0 = g(0 * x) = g(0) = 1.
      | zero => simp [g_one]
      | succ n ih =>
        -- g(x)^(n + 1) = g(x)^n * g(x) = g(n * x) * g(x) = g(n * x + x) = g((n + 1) * x).
        rw [pow_succ, ih, ← g_add]
        push_cast
        ring_nf
    -- The result follows from A^2015 = g(A 0 2)^2015 = g(2015 * A 0 2).
    simp [g_pow]