import Mathlib

/- The function $\varphi(x,y,z)$ defined for all triples $(x,y,z)$ of real numbers, is such that
there are two functions $f$ and $g$ defined for all pairs of real numbers, such that
\[\varphi(x,y,z) = f(x+y,z) = g(x,y+z)\]
for all real numbers $x,y$ and $z.$ Show that there is a function $h$ of one real variable,
such that \[\varphi(x,y,z) = h(x+y+z)\] for all real numbers $x,y$ and $z.$ -/

-- Define a theorem named algebra_85123 that takes a function φ mapping three real numbers to a real number
theorem algebra_85123 (φ : ℝ → ℝ → ℝ → ℝ)
    -- Given the existence of two functions f and g, each taking two real numbers,
    -- such that φ(x,y,z) equals both f(x+y,z) and g(x,y+z) for all x, y, z
    (hfg : ∃ f g : ℝ → ℝ → ℝ,
      ∀ x y z, φ x y z = f (x + y) z ∧ φ x y z = g x (y + z)) :
    -- Prove there exists a function h of one real variable such that φ(x,y,z) = h(x+y+z)
    ∃ h : ℝ → ℝ, ∀ x y z, φ x y z = h (x + y + z) := by
  -- Unpack the existential quantifier in hfg to obtain functions f and g and their properties
  rcases hfg with ⟨f, g, hfg_eq⟩
  -- Propose a candidate function h(t) defined as φ(0,0,t)
  use λ t => φ 0 0 t
  intro x y z
  -- Extract the left equality from hfg_eq: φ(x,y,z) = f(x+y,z)
  have h1 := (hfg_eq x y z).left
  -- Compute φ(0,0,x+y+z) using f: φ(0,0,x+y+z) = f(0+0,x+y+z) = f(0,x+y+z)
  have h2 := (hfg_eq 0 0 (x + y + z)).left
  -- Extract the right equality from hfg_eq: φ(x,y,z) = g(x,y+z)
  have h3 := (hfg_eq x y z).right
  -- Compute φ(0,0,x+y+z) using g: φ(0,0,x+y+z) = g(0,0+x+y+z) = g(0,x+y+z)
  have h4 := (hfg_eq 0 0 (x + y + z)).right
  -- Prove that g(x,y+z) = g(0,x+y+z) by leveraging the equalities
  have h5 : g x (y + z) = g 0 (x + y + z) := by
    -- Use φ(x,y,z) = f(x+y,z)
    have h6 := (hfg_eq x y z).left
    -- Use φ(0,x+y,z) = f(0+x+y,z) = f(x+y,z)
    have h7 := (hfg_eq 0 (x + y) z).left
    -- Use φ(x,y,z) = g(x,y+z)
    have h8 := (hfg_eq x y z).right
    -- Use φ(0,x+y,z) = g(0,x+y+z)
    have h9 := (hfg_eq 0 (x + y) z).right
    -- Simplify the expressions (this step is handled automatically by simp)
    simp at h6 h7 h8 h9
    -- Use linear arithmetic to deduce equality (details abstracted by linarith)
    linarith
  simp at h3 h4
  -- Combine the results using linear arithmetic to show φ(x,y,z) = h(x+y+z)
  linarith [h3, h4, h5]
