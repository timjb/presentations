# Aufbau der `lens`-Bibliothek

Das Hauptmodul der Bibliothek ist `Control.Lens`. In diesem Namespace wohnen die verschiedenen optischen Gerätschaften, wie zum Beispiel

* `Control.Lens.Lens`, die eigentlichen Lenses,
* `Control.Lens.Traversal`
* `Control.Lens.Setter`
* `Control.Lens.Iso`

Außerdem gibt es in diesem Namespace Module, welche Typklassen (`Control.Lens.Wrapped`, `Control.Lens.Tuple`), Hilfskonstruktionen (`Control.Lens.Reified`, `Control.Lens.TH`) oder nützliche Tools (`Control.Lens.Plated`, `Control.Lens.Level`) bereitstellen oder nur ausgewählte Funktionen (`Control.Lens.Combinators`, `Control.Lens.Operators`) oder Typen (`Control.Lens.Type`) exportieren.

Die Lens-Bibliothek stellt Lenses für viele Datenstrukturen aus anderen Standard-Haskell-Paketen (wie z.B. `text`, `bytestring` oder `containers`) zur Verfügung. Diese benutzen ihren jeweiligen Modulbezeichner mit `.Lens` hinten angehängt:

* `Data.ByteString.Lens`
* `Data.Text.Lens`
* `Data.Map.Lens`
* `Control.Exception.Lens`
