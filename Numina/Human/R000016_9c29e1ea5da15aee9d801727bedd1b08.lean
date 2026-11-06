import Mathlib

/- A rectangular solid has the following properties:
- If the length decreases by 2 cm, and the width and height remain unchanged, the volume decreases by 48 cubic cm.
- If the width increases by 3 cm, and the length and height remain unchanged, the volume increases by 99 cubic cm.
- If the height increases by 4 cm, and the length and width remain unchanged, the volume increases by 352 cubic cm.

Find the surface area of the original rectangular solid in square centimeters.-/
theorem algebra_4028 {l w h : ℚ} (hw : w ≠ 0) (hw' : 0 < w) (h1 : (l-2)*w*h=l*w*h-48) (h2 : l*(w+3)*h=l*w*h+99) (h3 : l*w*(h+4)=l*w*h+352) :
    2*(l*w+l*h+w*h) = 290 := by
  -- If the length decreases by 2 meters, the volume decreases by 48 cubic meters:
  --  \[
  --  (l - 2)wh = lwh - 48
  --  \]
  --  This simplifies to:
  --  \[
  --  lwh - 2wh = lwh - 48
  --  \]
  --  \[
  --  2wh = 48 \implies wh = 24
  --  \]
  have hhw : h*w=24 := by linarith
  -- If the width increases by 3 meters, the volume increases by 99 cubic meters:
  --  \[
  --  l(w + 3)h = lwh + 99
  --  \]
  --  This simplifies to:
  --  \[
  --  lwh + 3lh = lwh + 99
  --  \]
  --  \[
  --  3lh = 99 \implies lh = 33
  --  \]
  have hlh : l*h=33 := by linarith
  -- If the height increases by 4 meters, the volume increases by 352 cubic meters:
  --  \[
  --  lw(h + 4) = lwh + 352
  --  \]
  --  This simplifies to:
  --  \[
  --  lwh + 4lw = lwh + 352
  --  \]
  --  \[
  --  4lw = 352 \implies lw = 88
  --  \]
  have hlw : l*w=88 := by linarith
--   From \( wh = 24 \):
-- \[
-- h = \frac{24}{w}
-- \]
  have hsol_h : h=24/w := eq_div_of_mul_eq hw hhw
--   Substitute \( h \) into \( lh = 33 \):
-- \[
-- l \left(\frac{24}{w} \right) = 33 \implies \frac{24l}{w} = 33 \implies l = \frac{33w}{24} = \frac{11w}{8}
-- \]
  rw [hsol_h, mul_div_assoc', div_eq_iff hw, ← eq_div_iff (by norm_num)] at hlh
--   Substitute \( l \) and \( h \) into \( lw = 88 \):
-- \[
-- \left( \frac{11w}{8} \right) w = 88 \implies \frac{11w^2}{8} = 88 \implies 11w^2 = 704 \implies w^2 = \frac{704}{11} \implies w^2 = 64 \implies w = 8
-- \]
  rw [hlh] at hlw
  have : w^2=8^2 := by linarith
  rw [sq_eq_sq_iff_eq_or_eq_neg] at this
  rcases this with hwsol | hwsol
  -- w=-8 is impossible
  swap; linarith
--   Thus:
-- \[
-- w = 8
-- \]
-- Using \( w = 8 \) in \( h = \frac{24}{w} \):
-- \[
-- h = \frac{24}{8} = 3
-- \]
-- Finally, using \( w = 8 \) in \( l = \frac{11w}{8} \):
-- \[
-- l = \frac{11 \cdot 8}{8} = 11
-- \]
  rw [hwsol] at hsol_h hlh
  rw [hlh, hsol_h, hwsol]
  norm_num
