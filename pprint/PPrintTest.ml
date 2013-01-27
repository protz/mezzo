open PPrint

let d : document =
  string "Article: " ^^
  hang 2 (
  flow (words "Lors d'une réunion d'urgence
à Abidjan, les chefs d'état-major
de la Communauté économique
des Etats d'Afrique de l'Ouest (Cédéao)
ont par ailleurs décidé de relever le volume
de leurs effectifs promis au Mali, pour qu'ils
atteignent 5700 hommes, a déclaré à
la clôture le général Bakayoko,
dont le pays préside
actuellement la Cédéao. Jusque-là,
l'Afrique de l'Ouest visait
le déploiement d'environ 4 000 militaires.
Le Tchad s'est engagé à fournir 2 000 soldats, qui
ne font pas partie de la Misma mais agissent en coordination avec elle."))

let () =
  ToChannel.pretty 0.95 80 stdout d;
  flush stdout
