import Zen.Rng.Types



/-! # Random value generation -/
namespace Zen.Rng.Readme



/-- info:
0.532831
0.987008
0.957601
0.681761
0.965509
-/
#guard_msgs in #eval inIO <| Rng.runStdWith 0 do
  for _ in [0:5] do
    let f : Float ← gen [0 ; 1]
    println! "{f}"



/-- info:
-2092764894.958769
-1427314282.328239
-276630551.034491
-1502861091.002586
1964894377.998418
-/
#guard_msgs in #eval inIO <| Rng.runStdWith 0 do
  for _ in [0:5] do
    let f : Float ← gen
    println! "{f}"



/-- info:
[1, 3, 3, -7]
[-5, 10, 6]
[-2, 8]
[-2, 5, 4]
[3]
[-9]
[2, -9, 9]
[-10, -1]
[]
[-7, 4]
-/
#guard_msgs in #eval inIO <| Rng.runStdWith 0 do
  for _ in [0:10] do
    let l : List Int ← gen ([≤ 4], [-10 ; 10])
    println! "{l}"



/-- info:
[3, 3, -7]
[10, 6, 1]
[-2, 8, 3]
[-2, 5, 4]
[-9, -9, 3]
[2, -9, 9]
[-9, -10, -1]
[8, -7, 4]
[1, 10, -7]
[10, -10, -2]
-/
#guard_msgs in #eval inIO <| Rng.runStdWith 0 do
  for _ in [0:10] do
    let l : List Int ← gen ([= 3], [-10 ; 10])
    println! "{l}"



/-- info:
#[-3.645040, 9.705469, 3.435226]
#[-2.882394, 9.289219, 9.948282]
#[9.597480, 9.952867, 9.859118, 9.745261, 9.997723]
#[6.320418, -7.731713, 9.132686]
#[7.587625, 3.598145, 5.909291, 3.254650, 5.780256]
#[9.997005, 1.376065, 9.462767, -9.847182, 9.232222]
#[9.949910, 9.418275, 5.909902, 6.408307]
#[3.028664, 4.869220, 8.056388]
#[-4.706479, 9.743650, 9.980513]
#[7.339596, 7.543026, 5.555438, 1.824583, 6.289694]
-/
#guard_msgs in #eval inIO <| Rng.runStdWith 0 do
  for _ in [0:10] do
    let l : Array Float ← gen ([3 ; 5], [-10 ; 10])
    println! "{l}"
