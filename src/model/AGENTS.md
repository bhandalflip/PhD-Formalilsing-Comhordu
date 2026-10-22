# src/model/: rules for the model

- **The model** is the class `ComhModel` in `ComhBasics.v`. Its fields (`Mode`, `msgLatency`, `period`, `minDistComp`, …) are what `safety` assumes of a system. They are deliberately abstract: don't fix any of them in place.
