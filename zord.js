// This file was generated by lezer-generator. You probably shouldn't edit it.
import {Parser} from "lezer"
const spec_lowerid = {__proto__:null,open:8, type:14, extends:22, forall:54, true:84, false:86, undefined:88, override:98, let:122, in:124, letrec:128, if:134, then:136, else:138, trait:142, implements:144, inherits:146, new:152, toString:156}
const spec_upperid = {__proto__:null,Int:24, Double:26, String:28, Bool:30, Top:32, Bot:34, Trait:60, Array:62}
export const parser = Parser.deserialize({
  version: 13,
  states: "!$jO]QPOOOOQO'#E['#E[O]QPOOO!|QPO'#DQOOQO'#DR'#DRO%UQPO'#FUOOQO'#DZ'#DZO%qQPO'#FWOOQO'#D^'#D^O#hQPO'#F[OOQO'#FT'#FTO&sQQO'#FRO(]QPO'#DeO(kQPO'#DhOOQO'#FR'#FROOQO'#FQ'#FQO#hQPO'#FQO*QQQO'#FPO*mQPO'#DPOOQO'#Em'#EmOOQO'#E]'#E]O,bQPOOQOQPOOO.SQPO'#EjO(nQPO'#CbO.^QPO'#FSO.cQPO'#DjO.cQPO'#DmO#hQPO'#DpO.hQQO'#DtO#hQPO'#DyO.vQPO'#D{OOQO-E8Y-E8YO/nQPO'#FVO/vQPO'#FVO/}QPO,5;pO#hQPO'#DoOOQO'#Cq'#CqO0SQPO'#D`O.cQPO'#FZOOQO'#Db'#DbO0eQPO'#FYO0mQPO'#DaO0rQPO'#FXO0zQPO'#FXO1PQPO'#FXO1eQPO,5;rO%]QPO,5;rO1jQPO,5;vO1oQPO,5;nO.^QPO,5;nOOQO'#DQ'#DQOOQO'#Ez'#EzO(cQPO'#E|O2^QQO'#E}OOQO'#Ey'#EyOOQO'#Ec'#EcO2cQSO,5:POOQO'#Cd'#CdO(nQPO'#ExOOQO'#Ew'#EwOOQO'#Eb'#EbO2tQPO,5:SO3tQQO,5;lO#hQPO,5;lO#hQPO,5;lO#hQPO,5;lO#hQPO,5;lO#hQPO,5;lO#hQPO,5;lO#hQPO,5;lO#hQPO,5;lO4kQPO,5;kO*bQPO'#ExO4xQPO,59kO5SQPO,59kO#hQPO,59kO4kQPO,59kOOQO-E8Z-E8ZO5hQPO,5;UO5pQPO,5:ZO5uQPO,58|O6TQPO'#EfO6]QWO,5;nO8oQPO,5:UO8tQPO,5:XO8yQPO,5:[O#hQPO,5:`O9OQPO,5:`O9xQPO,5:`O:VQQO,5:`OOQO,5:e,5:eO:bQQO,5:gP;zQPO'#EjOOQO,5;O,5;OO<SQPO,5;qOOQO-E8b-E8bOOQO1G1[1G1[O<[QPO,59zO#hQPO,59zO<mQPO,5;uO=TQPO,5;tO0eQPO,59{OOQO,5;P,5;PO0eQPO,5;sO=[QPO,5;sO=dQPO,5;sOOQO-E8c-E8cOOQO1G1^1G1^O=iQPO1G1^OOQO1G1b1G1bOOQO'#Cn'#CnO=nQPO'#ErOOQO'#Co'#CoO4kQPO'#EtOOQO'#Eq'#EqOOQO1G1Y1G1YO=yQWO1G1YO@]QPO,5;hO@bQPO,5;iOOQO-E8a-E8aO#hQPO1G/kO@gQPO,5;dOOQO-E8`-E8`O#hQPO1G/nOOQO1G1W1G1WOA|QQO1G1WOBWQQO1G1WOCuQQO1G1WOC|QQO1G1WOEhQQO1G1WOEoQQO1G1WOFhQQO1G1WOGbQPO'#EpOOQO'#Eo'#EoOHvQPO1G1VO(kQPO'#EoOIQQPO'#EoO1oQPO'#EoOIVQPO1G/VO#hQPO1G/VO4kQPO1G/VOIkQPO1G/VOIpQPO1G/VOOQO1G0p1G0pO#hQPO1G/uO(nQPO'#EnOOQO'#E^'#E^OI{QPO1G.hOOQO'#E_'#E_OJOQPO1G.hO4kQPO1G.hO4kQPO1G.hOOQO'#Dc'#DcOOQO,5;Q,5;QOOQO-E8d-E8dO#hQPO1G/pO4kQPO1G/sO#hQPO1G/vOJZQQO1G/zOKuQQO1G/zOK|QQO'#EpOMrQQO1G/zO#hQPO1G/zO9OQPO1G/zO9xQPO1G/zPNQQPO,5;UPNVQPO'#EdO#hQPO1G/fOOQO1G/f1G/fO4kQPO1G1aON[QPO1G1`OOQO1G1`1G1`ONcQPO1G1`OOQO1G/g1G/gONhQPO1G1_O0eQPO1G1_PNpQPO'#EePNuQPO'#EeOOQO7+&x7+&xONzQPO'#EsO! PQPO'#EsO! [QPO,5;^O! aQPO,5;`O4kQPO1G1SOOQO1G1T1G1TOOQO7+%V7+%VO4kQPO1G1OOOQO7+%Y7+%YO1oQPO'#EuOOQO'#Ea'#EaO! lQPO,5;[O4kQPO,5;ZO4kQPO,5;ZO!!fQPO,5;ZOOQO,5;Z,5;ZO#hQPO7+$qO4kQPO7+$qO!!qQPO7+$qO!!vQPO7+$qOOQO7+$q7+$qOOQO7+%a7+%aO!#RQPO,5;YOOQO-E8[-E8[O!#WQPO7+$SO4kQPO7+$SO4kQPO7+$SOOQO-E8]-E8]O!#cQPO7+$SO!#nQPO7+$SO!#yQPO7+%[O!$OQPO7+%_O!$ZQPO7+%bO#hQPO7+%fO!$`QQO,5;[O9OQPO7+%fO!&UQQO7+%fO!&{QQO7+%fO!'SQQO7+%fO!'bQQO1G1VOOQO7+%Q7+%QO!(hQPO7+&{OOQO7+&z7+&zO!(sQPO7+&zOOQO7+&V7+&VO!(xQPO7+&yP0eQPO,5;PO4kQPO,5;_O!)QQPO,5;_OOQO-E8^-E8^OOQO1G0x1G0xOOQO1G0z1G0zO!)VQPO7+&nO!)bQPO7+&jO!)mQPO'#EvO!)uQPO,5;aOOQO-E8_-E8_O!*fQPO1G0uOOQO1G0u1G0uO4kQPO1G0uO!*sQPO<<H]O!*xQPO<<H]OOQO<<H]<<H]O#hQPO<<H]OOQO1G0t1G0tO4kQPO<<GnO4kQPO<<GnO!+TQPO<<GnO!+`QPO<<GnOOQO<<Gn<<GnO#hQPO<<HvO#hQPO<<HyO#hQPO<<H|O!+kQQO<<IQO!,bQQO1G0uO!-kQQO<<IQO#hQPO<<IQO9OQPO<<IQOOQO<<Jg<<JgOOQO<<Jf<<JfP!-rQPO1G0kO!-wQPO1G0yO4kQPO1G0yP!.VQPO'#E`OOQO<<JY<<JYOOQO<<JU<<JUO1oQPO,5;bOOQO1G0{1G0{O!.vQPO7+&aOOQOAN=wAN=wO#hQPOAN=wO!/TQPOAN=wO!/YQPOAN=YO!/eQPOAN=YOOQOAN=YAN=YO4kQPOAN=YOOQOAN>bAN>bO!/pQPOAN>eOOQOAN>hAN>hO#hQPOAN>lO!/uQQO7+&aO!1OQQOAN>lO!1uQQOAN>lOOQO7+&Q7+&QO!1|QPO7+&eP4kQPO,5:zOOQO1G0|1G0|O!2[QPOG23cOOQOG23cG23cOOQOG22tG22tO4kQPOG22tO!2aQPOG22tO#hQPOG24PO!2lQQOG24WO#hQPOG24WP!3cQPO1G0fOOQOLD(}LD(}O!3nQPOLD(`OOQOLD(`LD(`OOQOLD)kLD)kO!3yQQOLD)rOOQO!$'Kz!$'KzO!4pQQO'#FPO#hQPO'#DyO9OQPO,5;lO9OQPO,5;lO9OQPO,5;lO9OQPO,5;lO9OQPO,5;lO9OQPO,5;lO9OQPO,5;lO9OQPO,5;lO9xQPO,5;kO9OQPO,5:`O#hQPO1G/kO#hQPO1G/nO!5uQQO1G1WO!6PQQO1G1WO!7OQQO1G1WO!7VQQO1G1WO!8RQQO1G1WO!8YQQO1G1WO!9RQQO1G1WO#hQPO1G/uO!9]QQO1G/zO9OQPO1G/zO9xQPO,5;ZO9xQPO,5;ZO9OQPO7+%fO!9dQQO7+%fO9xQPO1G0uO#hQPO<<HvO#hQPO<<H|O!9kQQO<<IQO9OQPO<<IQO9OQPOAN>lO!9rQQOAN>lO#hQPOG24PO!9yQQOG24WO9OQPOG24WO!:QQQOLD)rO9OQPO'#FQO!:XQQO'#FPO!:fQQO'#DtO!:tQSO,5:PO!;VQPO,5:SO!;bQQO,5;lO!;iQPO,5:ZO!;nQQO,5:`O!;yQQO1G/zO!<QQQO1G/zO!<`QPO,5;ZO!<kQPO7+%[O!<pQPO7+%bO!<uQQO7+%fO!<|QQO7+%fO!=[QQO<<IQO!=cQPOAN>eO!=hQQOAN>lO(]QPO'#DeO(kQPO'#DhO#hQPO'#DoO9OQPO,5:`O9xQPO,5:`O(kQPO'#EoO#hQPO1G/pO#hQPO1G/vO9OQPO1G/zO9xQPO1G/zO9OQPO7+%fO#hQPO<<HyO9OQPO<<IQO!=oQPO,5:UO!=tQPO,5:[O!=yQPO7+%_O.cQPO'#DjO#hQPO'#DpO4kQPO1G/sO!>UQPO,5:XO.cQPO'#Dm",
  stateData: "!>^~O#]OSPOSQOS~OSgOVhOdVOhXOvYOwYOxYOyYOzYO{YO|YO!OTO!Y[O!]]O!_jO!bkO!elO!imO!nnO!poO!q`O!r`O!s`O#_RO#`SO~OdtXftXhtXmuXrtX#_tX#`tX#otX~OStOdVOhXOvYOwYOxYOyYOzYO{YO|YO!OTO!Y[O!]]O!_jO!bkO!elO!imO!nnO!poO!q`O!r`O!s`O#_SO#`SO~O!P#yP~P#hOhyO!OwO#_uO#`uO#o|Og#{P~O!R!PO~P%]OdVOhXOvYOwYOxYOyYOzYO{YO|YO!OTO!W!RO#_SO#`SO~Of#uX!Y#uX!q#uX!t#uX!u#uX!v#uX!w#uX!x#uX!y#uX!z#uX!{#uX!|#uX!}#uX#Z#uXT#uX!P#uXi#uX!`#uX!f#uX!l#uXg#uX!g#uX~P%xOd!WOh!VO#_!TO#o!UO~Oh!]O#`![O~O!q!dO!t!bO!u!cO!v!cO!w!dO!x!eO!y!fO!z!gO!{!hO!|!hO!}!iO#Z#sXT#sX!P#sXi#sX!`#sX!f#sXg#sX!g#sX~Of!jO!Y!jO~P(sOd!WOh!kO#_!TO#`![O#o!UO~Of!oOr!nO~P*[OStOdVOhXOvYOwYOxYOyYOzYO{YO|YO!OTO!Y[O!]]O!_jO!bkO!elO!imO!nnO!poO!q`O!r`O!s`O#`SO~OVhO#_RO~P*wOStOdVOhXOvYOwYOxYOyYOzYO{YO|YO!OTO!Y[O!]]O!_jO!bkO!elO!imO!nnO!poO!q`O!r`O!s`O~O#_!qO#`!qO~P,lOm!tO~O#_!TO~O!OwO!j!{O!k!zO!l!yO~OdVOhXOvYOwYOxYOyYOzYO{YO|YO!OTO#_SO#`SO~OT#QO!P#yX~O!P#yX~P#hO!P#TO~Od!WOh!VOr#VO#_!TO#o!UO~O#_uO#`uO~Om#YO~OT#ZOg#{X~Om#[O~OhyO!OwO#_uO#`uO#o#^Og#{X~Og#`O~Oi#bO~O[#gO]#gO^#gO_#gO`#gOa#gOd#dOh#fO#`#cO~O#r#kO~Od!WOh!VO!Z#mO#_!TO#o!UO~Oh!]Om#pO#`![O~O!q!dO!t!bO!u!cO!v!cO!w!dO!x!eO!y!fO!z!gO!{!hO!|!hO!}!iO~Of#ta!Y#ta#Z#taT#ta!P#tai#ta!`#ta!f#tag#ta!g#ta!l#ta~P3POk#|On#}Oo$OO~P1oOf$ROr$QO~P*[Od!WOf$ROh!VOr$QO#_!TO#o!UO~OT$UOmuX~O!`$VO~OX$WOZ$^Or$]O#`![O~O#_$_O#`$_O~Om!tOd#vaf#vah#vav#vaw#vax#vay#vaz#va{#va|#va!O#va!W#va!Y#va!q#va!t#va!u#va!v#va!w#va!x#va!y#va!z#va!{#va!|#va!}#va#Z#va#_#va#`#vaT#va!P#vai#va!`#va!f#va!l#vag#va!g#va~Or$bO~Of$cO~O!f$dO~OS(wO!Y(uO!](vO!_)VO!b)ZO!e)WO!i(eO!n'kO!poO!q(cO!r(cO!s(cO~P.vOk(zOn#}Oo$OO~P1oO!j$kO!k$jO!l$iO~Of!oa!Y!oa!q!oa!t!oa!u!oa!v!oa!w!oa!x!oa!y!oa!z!oa!{!oa!|!oa!}!oa#Z!oaT!oa!P!oai!oa!`!oa!f!oa!l!oag!oa!g!oa~P%xO#_$lO#`$lO~OT#QO!P#ya~Od!WOh!VOr$nO#_!TO#o!UO~Of$pO~Od!WOh!VO!OwO#_!TO#o!UO~Oi$rO~P<rOT#ZOg#{a~Om$vO~Og$yO~O#_uO#`uOg#gP~Om!tOd#vif#vih#viv#viw#vix#viy#viz#vi{#vi|#vi!O#vi!W#vi!Y#vi!q#vi!t#vi!u#vi!v#vi!w#vi!x#vi!y#vi!z#vi!{#vi!|#vi!}#vi#Z#vi#_#vi#`#viT#vi!P#vii#vi!`#vi!f#vi!l#vig#vi!g#vi~Of%OO~Og%PO~Ol%RO~O!t!bOf#ti!Y#ti!q#ti!w#ti!x#ti!y#ti!z#ti!{#ti!|#ti!}#ti#Z#tiT#ti!P#tii#ti!`#ti!f#tig#ti!g#ti!l#ti~O!u#ti!v#ti~P@lO!u!cO!v!cO~P@lO!q!dO!t!bO!u!cO!v!cO!w!dOf#ti!Y#ti!y#ti!z#ti!{#ti!|#ti!}#ti#Z#tiT#ti!P#tii#ti!`#ti!f#tig#ti!g#ti!l#ti~O!x#ti~PBbO!x!eO~PBbO!q!dO!t!bO!u!cO!v!cO!w!dO!x!eO!y!fO!z!gOf#ti!Y#ti!|#ti!}#ti#Z#tiT#ti!P#tii#ti!`#ti!f#tig#ti!g#ti!l#ti~O!{#ti~PDTO!{!hO~PDTO!q!dO!t!bO!u!cO!v!cO!w!dO!x!eO!y!fO!z!gO!{!hO!|!hO~Of#ti!Y#ti!}#ti#Z#tiT#ti!P#tii#ti!`#ti!f#tig#ti!g#ti!l#ti~PEvOX%TOp#dXq#dX#Z#dXr#dXT#dX!P#dXi#dX!`#dX!f#dXg#dX!g#dX~P1oO#Z#siT#si!P#sii#si!`#si!f#sig#si!g#si~Op%WOq%XO~PH[OX%TO~Od!WOf%]Oh!VOr%[O#_!TO#o!UO~OT%`O~Op%WOq%XOr%[O~OX$WOZ%fOr%eO#`![O~Of!hi!Y!hi#Z!hiT!hi!P!hii!hi!`!hi!f!hig!hi!g!hi!l!hi~P3PO!q'nO!t'lO!u'mO!v'mO!w'nO!x'oO!y'pO!z'qO!{'rO!|'rO!}'sO~O!l%mO~PKQOX%TOp#dXq#dX!k#dX!l#dXf#dX!Y#dX!q#dX!t#dX!u#dX!v#dX!w#dX!x#dX!y#dX!z#dX!{#dX!|#dX!}#dX#Z#dXT#dX!P#dXi#dX!`#dX!f#dXg#dX!g#dX~P1oOp(SOq(TO!k%oO!l%mO~OT$UO~OT#QO~Oi%vO~P<rOi%vO~OT%xOg#{i~OT#ZO~Om%zO~Of%{O~O#_uO#`uOg#gX~Og&OO~Oi&POp%WOq%XO~OX%TOp#daq#da#Z#dar#daT#da!P#dai#da!`#da!f#dag#da!g#da~P1oOh!]Om&XO#`![O~OT&[O~Op%WOq%XOr&]O~OY&^O~OZ&`Or&_O#`![O~OT&cOp%WOq%XO~Op%WOq%XOr&_O~O!`&dO~Op%WOq%XOr&eO~O!g&fO~OX%TOp#daq#da!k#da!l#daf#da!Y#da!q#da!t#da!u#da!v#da!w#da!x#da!y#da!z#da!{#da!|#da!}#da#Z#daT#da!P#dai#da!`#da!f#dag#da!g#da~P1oOf!hq!Y!hq#Z!hqT!hq!P!hqi!hq!`!hq!f!hqg!hq!g!hq!l!hq~P3PO!l&jO~PKQOp(SOq(TO!k&kO!l&jO~Op(SOq(TOf#si!Y#si!q#si!t#si!u#si!v#si!w#si!x#si!y#si!z#si!{#si!|#si!}#si!l#si~PH[Op%WOq%XO!P&lO~Oi&mO~OT%xOg#{q~Of&pO~Oi&rOp%WOq%XO~Oi&sOp%WOq%XO~Oj&tOY#jX~OY&uO~O#Z#ciT#ci!P#cii#ci!`#ci!f#cig#ci!g#ci~Op%WOq%XOr#ci~P!)zOT&wO~Op%WOq%XOr&xO~OT&|Op%WOq%XO~Op%WOq%XOr&}O~Of!hy!Y!hy#Z!hyT!hy!P!hyi!hy!`!hy!f!hyg!hy!g!hy!l!hy~P3POp(SOq(TO!k#ci!l#cif#ci!Y#ci!q#ci!t#ci!u#ci!v#ci!w#ci!x#ci!y#ci!z#ci!{#ci!|#ci!}#ci~P!)zO!l'RO~PKQOT%xO~OT'VOp%WOq%XOg#gi~Of'XO~O#Z#cqT#cq!P#cqi#cq!`#cq!f#cqg#cq!g#cq~Op%WOq%XOr#cq~P!.[OT'[O~OT']Op%WOq%XO~Op%WOq%XOr'^O~O!`'`O~Op(SOq(TO!k#cq!l#cqf#cq!Y#cq!q#cq!t#cq!u#cq!v#cq!w#cq!x#cq!y#cq!z#cq!{#cq!|#cq!}#cq~P!.[Of!h!R!Y!h!R#Z!h!RT!h!R!P!h!Ri!h!R!`!h!R!f!h!Rg!h!R!g!h!R!l!h!R~P3PO!l'bO~PKQOT'VOp%WOq%XOg#gq~OT'dO~OT'fOp%WOq%XO~Of!h!Z!Y!h!Z#Z!h!ZT!h!Z!P!h!Zi!h!Z!`!h!Z!f!h!Zg!h!Z!g!h!Z!l!h!Z~P3POT'VOp%WOq%XO~OT'iOp%WOq%XO~Of!h!c!Y!h!c#Z!h!cT!h!c!P!h!ci!h!c!`!h!c!f!h!cg!h!c!g!h!c!l!h!c~P3POf'tO!Y'tOf#sX!Y#sX!l#sX~P(sO!t'lO!l#ti!q#ti!w#ti!x#ti!y#ti!z#ti!{#ti!|#ti!}#ti~O!u#ti!v#ti~P!5TO!u'mO!v'mO~P!5TO!q'nO!t'lO!u'mO!v'mO!w'nO!l#ti!y#ti!z#ti!{#ti!|#ti!}#ti~O!x#ti~P!6ZO!x'oO~P!6ZO!q'nO!t'lO!u'mO!v'mO!w'nO!x'oO!y'pO!z'qO!l#ti!|#ti!}#ti~O!{#ti~P!7^O!{'rO~P!7^O!q'nO!t'lO!u'mO!v'mO!w'nO!x'oO!y'pO!z'qO!{'rO!|'rO~O!l#ti!}#ti~P!8aO!l!hi~PKQO!l!hq~PKQO!l!hy~PKQO!l!h!R~PKQO!l!h!Z~PKQO!l!h!c~PKQOf'tO!Y'tO!l#sX~P3PO!OwO!j(yO!k(xO!l'uO~Od!WOh!VO!Z'vO#_!TO#o!UO~Oh!]Om'wO#`![O~O!l#ta~PKQO!`(PO~O!j)OO!k(}O!l(RO~O!l(UO~PKQOp(SOq(TO!k)PO!l(UO~Oh!]Om(WO#`![O~O!`(XO~O!g(YO~O!l([O~PKQOp(SOq(TO!k)RO!l([O~O!l(]O~PKQO!`(_O~O!l(aO~PKQOr({O~O!f(|O~Op%WOq%XOr)QO~Of)XO~O!q!y~",
  goto: "Ck$PPPPPPP$QP$VPPPPPPPPP$s$sP%oPPPPPPPPPPPPP$Q&R&wPPPPPPP&wPP&wP(l)P)W)kP)nPP)nP)nPP)nP)n)nPPP)nPPPP)nP)nPPPPPPPPPPPPPP+`+f+m+s+},T,_,u-a-g-nPPP-xPP-|.R.V0X0{2T3P$s3S3]3`3l3x4WP4j4jP4x6z:^<O=s?jA_AbCVC]Cb&wVcOQed!^]b!`!l#|%Y(g(m(v(zQ!shS#n!]!kW$Z!s$Y$[%dR%b$W!s#g!R!j!o!{#f#y$O$R$]$^$c$g$k$p%O%R%T%V%W%X%]%e%f%n%{&X&_&`&p&t&}'X'^'t(S(T(W(y)O)X^vV}!P#Y#[$v%zQ#XyQ$z#dR%|${UbOQel!U[bv!V!Z!k!l!m#U#X$P$q(f(uQ!vjQ!wkQ#WwQ)S)VR)Y)Z$eYOQTXZ`eglnort!b!c!d!e!f!g!h!i!n!y!z#O#V#m#p$Q$V$b$d$i$j$n%[%m%o&]&d&e&f&j&k&x'R'`'b'k'l'm'n'o'p'q'r's'u'v'w(P(R(U(X(Y([(](_(a(c(w(x({(|(})P)Q)R)WS{V!PQ#]}Q$t#YQ$u#[Q%y$vR&n%zS{V!PR#]}S|V!PQ!|mQ#^}Q$s#XQ%w$qR(j(eR$`!t$_^OQTX`eglnrt!b!c!d!e!f!g!h!i!n!y!z#V#m#p$Q$V$b$d$i$j$n%[%m%o&]&d&e&f&j&k&x'R'`'b'k'l'm'n'o'p'q'r's'u'v'w(P(R(U(X(Y([(](_(a(c(w(x({(|(})P)Q)R)WQQORpQSeOQR!peQ$Y!sR%c$YQ$[!sQ%d$YT%g$[%dQ${#dR%}${Q%V#yQ%n$gT&U%V%nQ!`]Q!lbY#o!`!l%Y(g(mQ%Y#|Q(g(vR(m(zQ!Z[Q!mbQ#Uv[#l!Z!m#U$P$q(fQ$P!lQ$q#XR(f(uQrTR#SrS}V!PR#_}Q!uiQ#i!ST$a!u#iTPOQVdOQeT$X!s$YQ#{!jQ$T!oQ$h!{Q$}#fQ%_$RQ%h$]Q%i$^Q%k$cQ%r$kQ%s'tQ%u$pQ&Q%OQ&R%RQ&V%WS&W%X(TQ&Z%]Q&a%eQ&b%fQ&h(SQ&o%{Q&v&XQ&z&_Q&{&`Q'S(WQ'W&pQ'_&}Q'c'XQ'e'^Q(l(yQ(q)OR)U)X!c#z!j!o!{#f$R$]$^$c$k$p%O%R%W%X%]%e%f%{&X&_&`&p&}'X'^'t(S(T(W(y)O)XQ#h!R!Q#y!j!o#f$R$]$^$c$p%O%R%W%X%]%e%f%{&X&_&`&p&}'X'^)X`$g!{$k't(S(T(W(y)OW%U#y$g%V%nQ%Z$OQ&S%TR'Y&t!s#e!R!j!o!{#f#y$O$R$]$^$c$g$k$p%O%R%T%V%W%X%]%e%f%n%{&X&_&`&p&t&}'X'^'t(S(T(W(y)O)XR$|#dW%U#y$g%V%nR%Z#}R&T%Te!_]b!`!l#|%Y(g(m(v(ze!^]b!`!l#|%Y(g(m(v(zi!Y[bv!Z!l!m#U#X$P$q(f(uh!X[bv!Z!l!m#U#X$P$q(f(uT#j!V!ki!X[bv!Z!l!m#U#X$P$q(f(uUfOQeQqTQ!QXS!rgtQ!xlS!}n'kQ#RrQ$S!nQ$o#VS%Q#m'vS%S#p'wQ%^$QS%a$V(PQ%j$bQ%l$dQ%t$nQ&Y%[Q&y&]S'O&d(XQ'P&eS'Q&f(YQ'Z&xS'g'`(_Q(i(wQ(n({Q(o(|Q(s)QR)T)W!QaOQTXeglrt!n#V$Q$b$d$n%[&]&e&x(w({(|)Q)WQ!a`S#q!b'lQ#r!cQ#s!dQ#t!eQ#u!fQ#v!gQ#w!hQ#x!iQ$e!yQ$f!zQ%p$iQ%q$jQ&g%mQ&i%oQ'T&jQ'U&kQ'a'RQ'h'b^'jn#m#p$V&d&f'`Q'x'mQ'y'nQ'z'oQ'{'pQ'|'qQ'}'rQ(O'sQ(Q'uQ(V(RQ(Z(UQ(^([Q(`(]Q(b(a^(d'k'v'w(P(X(Y(_Q(h(cQ(k(xQ(p(}Q(r)PR(t)R$__OQTX`eglnrt!b!c!d!e!f!g!h!i!n!y!z#V#m#p$Q$V$b$d$i$j$n%[%m%o&]&d&e&f&j&k&x'R'`'b'k'l'm'n'o'p'q'r's'u'v'w(P(R(U(X(Y([(](_(a(c(w(x({(|(})P)Q)R)W$^ZOQTX`eglnrt!b!c!d!e!f!g!h!i!n!y!z#V#m#p$Q$V$b$d$i$j$n%[%m%o&]&d&e&f&j&k&x'R'`'b'k'l'm'n'o'p'q'r's'u'v'w(P(R(U(X(Y([(](_(a(c(w(x({(|(})P)Q)R)WR#Oo$`iOQTX`eglnort!b!c!d!e!f!g!h!i!n!y!z#V#m#p$Q$V$b$d$i$j$n%[%m%o&]&d&e&f&j&k&x'R'`'b'k'l'm'n'o'p'q'r's'u'v'w(P(R(U(X(Y([(](_(a(c(w(x({(|(})P)Q)R)WT!SZ#O$eUOQTXZ`eglnort!b!c!d!e!f!g!h!i!n!y!z#O#V#m#p$Q$V$b$d$i$j$n%[%m%o&]&d&e&f&j&k&x'R'`'b'k'l'm'n'o'p'q'r's'u'v'w(P(R(U(X(Y([(](_(a(c(w(x({(|(})P)Q)R)WRsT$eWOQTXZ`eglnort!b!c!d!e!f!g!h!i!n!y!z#O#V#m#p$Q$V$b$d$i$j$n%[%m%o&]&d&e&f&j&k&x'R'`'b'k'l'm'n'o'p'q'r's'u'v'w(P(R(U(X(Y([(](_(a(c(w(x({(|(})P)Q)R)WQ!OVR#a!PVzV}!P_xVm}!P#X$q(e",
  nodeNames: "⚠ LineComment BlockComment Program open ; TypeDef type TypeNameDecl < > extends Int Double String Bool Top Bot TypeName RecordType { LabelDecl : } ( ) % forall * . Trait Array TypeOp TypeOp = TermDef TermNameDecl TermName Number String Document Unit true false undefined Array [ ] Record override RecordField MethodPattern SelfAnno Label @ Lambda \\ -> BigLambda /\\ Let let in LetRec letrec Open IfElse if then else Trait trait implements inherits TraitArrow New new ToString toString ArithOp LogicOp LengthOp IndexOp ArithOp ArithOp ArithOp AppendOp CompareOp LogicOp LogicOp ForwardOp MergeOp",
  maxTerm: 138,
  skippedNodes: [0,1,2],
  repeatNodeCount: 11,
  tokenData: "1[~RzX^#upq#uqr$jrs%Pst%suv%xvw&Pxy&^yz&kz{&p{|&w|}'U}!O'Z!O!P'x!P!Q(V!Q!R(d!R![*R![!],W!]!^,]!^!_,b!_!`,l!`!a,|!b!c-W!c!}-]!}#O-q#O#P-v#P#Q-{#Q#R.Q#R#S.V#S#T.[#T#o.m#o#p/R#p#q0z#q#r1V#y#z#u$f$g#u#BY#BZ#u$IS$I_#u$I|$JO#u$JT$JU#u$KV$KW#u&FU&FV#u~#zY#]~X^#upq#u#y#z#u$f$g#u#BY#BZ#u$IS$I_#u$I|$JO#u$JT$JU#u$KV$KW#u&FU&FV#uZ$oQ!rPqr$u!_!`$zY$zO!tYY%PO!yY~%UUw~OY%PZr%Prs%hs#O%P#O#P%m#P~%P~%mOw~~%pPO~%P~%xO!s~~&POj~!v~~&UPq~vw&X~&^O!z~~&cPh~yz&f~&kOy~~&pOi~Z&wOlP!uY~&|P!w~{|'P~'UO!x~~'ZO!}~~'`Q!qZ}!O'f!`!a'q~'kQP~OY'fZ~'fV'xO!ZSpRZ'}PmX!O!P(QQ(VO#rQZ([P!uY#O#P(_P(dO!]P~(iWv~!O!P)R!Q![*R!g!h)g!q!r*d!z!{*r#X#Y)g#c#d+^#l#m+l~)UP!Q![)X~)^Rv~!Q![)X!g!h)g#X#Y)g~)jR{|)s}!O)s!Q![)y~)vP!Q![)y~*OPv~!Q![)y~*WSv~!O!P)R!Q![*R!g!h)g#X#Y)g~*gP!Q!Y*j~*oPv~!Q!Y*j~*uR!Q![+O!c!i+O#T#Z+O~+TRv~!Q![+O!c!i+O#T#Z+O~+aP!Q!Y+d~+iPv~!Q!Y+d~+oR!Q![+x!c!i+x#T#Z+x~+}Rv~!Q![+x!c!i+x#T#Z+x~,]Of~~,bOT~~,iPX~!yY!_!`$zZ,qQrP!_!`$z!`!a,wY,|O!lYZ-TPYP!yY!_!`$z~-]O!W~~-bT#`~wx-]!Q![-]!c!}-]#R#S-]#T#o-]~-vO!O~~-{O!Y~~.QO!P~~.VO!|~~.[O#o~~._RO#S.[#S#T.h#T~.[~.mOx~~.rT#_~wx.m!Q![.m!c!}.m#R#S.m#T#o.m~/WPd~}!O/Z~/^UO}/Z}!O/p!O;'S/Z;'S;=`0t<%l?Ar/Z?As~/Z~/sWO}/Z}!O/p!O#q/Z#q#r0]#r;'S/Z;'S;=`0t<%l?Ar/Z?As~/Z~0bUQ~O}/Z}!O/p!O;'S/Z;'S;=`0t<%l?Ar/Z?As~/Z~0wP;=`<%l/Z~0}P#p#q1Q~1VO!{~~1[Og~",
  tokenizers: [0, 1, 2, 3],
  topRules: {"Program":[0,3]},
  specialized: [{term: 107, get: value => spec_lowerid[value] || -1},{term: 108, get: value => spec_upperid[value] || -1}],
  tokenPrec: 3461
})
