import Mathlib
/- Suppose

$$
h \cdot a \cdot r \cdot v \cdot a \cdot r \cdot d=m \cdot i \cdot t=h \cdot m \cdot m \cdot t=100 .
$$

Find $(r \cdot a \cdot d) \cdot(t \cdot r \cdot i \cdot v \cdot i \cdot a)$. -/
theorem algebra_610348 (h a r v m i t : ℝ) (h1 : h * a * r * v * a * r * d = m * i * t) (h2 : m * i * t = h * m * m * t) (h3 : h * m * m * t = 100) : (r * a * d) * (t * r * i * v * i * a) = 10000:= by
  -- Use h2 and h3 to substitute in h1
  rw [h2, h3] at h1
  -- Use h3 to substitute in h2
  rw [h3] at h2
  -- Multiply both sides by (m·i·t)² to get h·a·r·v·a·r·d·(m·i·t)² = 1000000
  replace h1 : h * a * r * v * a * r * d * (m * i * t) ^ 2 = 1000000:= by
    rw [h1, h2]
    linarith
  -- Rearrange the left side to match our goal using ring tactic
  rw [show h * a * r * v * a * r * d * (m * i * t) ^ 2 = r * a * d * (t * r * i * v * i * a) * (h * m * m * t) by ring] at h1
  -- Use h3 to substitute h·m·m·t with 100
  rw [h3] at h1
  -- Complete the proof using linear arithmetic
  linarith
