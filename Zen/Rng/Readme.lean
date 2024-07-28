import Zen.Rng.Types



/-! # Random value generation -/
namespace Zen.Rng.Readme


#eval inIO <| Rng.runStdWith 0 do
  for _ in [0:5] do
    let f : Float ← gen [0 ; 1]
    println! "{f}"

#eval inIO <| Rng.runStdWith 0 do
  for _ in [0:5] do
    let f : Float ← gen
    println! "{f}"

#eval inIO <| Rng.runStdWith 0 do
  for _ in [0:10] do
    let l : List Int ← gen ([≤ 4], [-10 ; 10])
    println! "{l}"

#eval inIO <| Rng.runStdWith 0 do
  for _ in [0:10] do
    let l : List Int ← gen ([3], [-10 ; 10])
    println! "{l}"

#eval inIO <| Rng.runStdWith 0 do
  for _ in [0:50] do
    let l : Array Float ← gen ([3 ; 5], [-10 ; 10])
    println! "{l}"
