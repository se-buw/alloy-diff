abstract sig Light {
   var color : one Color,
   var car : lone Car
} {
   always (some car implies eventually color = RED)
}

sig Car {}
enum Color {GREEN, RED}

// concrete traffic lights in the scenario
one sig LightA, LightB extends Light {}

pred crash {
   LightA.color = GREEN and LightB.color = GREEN
}

fact initiallyBothRed {
   Light.color = RED
}

assert neverCrash {always not crash}

check neverCrash
