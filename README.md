# Formalized Proof of geometric concept of epicycles in planetary orbits

This is my first large project in the Coq Proof Assistant. :)

## 1. DEFINITIONS.V: Create definitions of each structure and function mentioned in the
paper
a. This includes points, vectors, vector operations
  i. As well as the epicycle and deferent circles themselves.
b. A base for trigonometric functions
  i. I attempted to make this simpler after trying it a different way formerly.
    1. My thought was to split it into quadrants (like on an X-Y plane),
    and determine from placement in these quadrants, which direction
    the planet was moving in
c. A model for motion
  i. This included the information assigned to a planet
    1. Orbit radii, velocities...
  ii. Calculation functions for its position at some time t
    1. What angle it is from the observation point
      a. Where the angle is given as a quadrant (1, 2, 3, or 4)
  iii. Apparent motion direction over a time interval
d. Retrograde condition
  i. This is the condition that must be satisfied for retrograde motion to occur
  ii. It is a relationship between the angular velocities and the radii
## 2. LEMMAS.V: Set up the base lemmas from which we can prove retrograde motion
a. The idea is we will see:
  i. Forward motion → stop → backwards motion (1 → 0 → -1)
b. There is some complicated geometric proofs in the paper, which is why these are
admitted. I attempted the ones I thought were achievable, which are those seen
in INSCRIBEDANGLE.V
## 3. RETROGRADE.V: relates the retrograde condition to Apollonius’ condition.
a. Proofs if and only if apollonius' condition and the retrograde condition
  i. A discussion on why this was admitted is given above.
b. An example of values that satisfy the retrograde condition given
