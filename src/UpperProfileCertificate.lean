import UpperProfileCertificateData0
import UpperProfileCertificateData1
import UpperProfileCertificateData2
import UpperProfileCertificateData3
import UpperProfileCertificateData4
import UpperProfileCertificateData5
import UpperProfileGridSoundness

set_option autoImplicit false
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
noncomputable section
namespace UpperProfileCertificate
open UpperProfileGridArithmetic UpperProfileGridStorage UpperProfileGridSoundness
noncomputable def rowPrefix (i : ℕ) : ℕ → ℕ := (if i<360 then (if i<180 then (if i<90 then (if i<45 then (if i<22 then (if i<11 then (if i<5 then (if i<2 then (if i<1 then UpperProfileCertificateData.prefix0 else UpperProfileCertificateData.prefix1) else (if i<3 then UpperProfileCertificateData.prefix2 else (if i<4 then UpperProfileCertificateData.prefix3 else UpperProfileCertificateData.prefix4))) else (if i<8 then (if i<6 then UpperProfileCertificateData.prefix5 else (if i<7 then UpperProfileCertificateData.prefix6 else UpperProfileCertificateData.prefix7)) else (if i<9 then UpperProfileCertificateData.prefix8 else (if i<10 then UpperProfileCertificateData.prefix9 else UpperProfileCertificateData.prefix10)))) else (if i<16 then (if i<13 then (if i<12 then UpperProfileCertificateData.prefix11 else UpperProfileCertificateData.prefix12) else (if i<14 then UpperProfileCertificateData.prefix13 else (if i<15 then UpperProfileCertificateData.prefix14 else UpperProfileCertificateData.prefix15))) else (if i<19 then (if i<17 then UpperProfileCertificateData.prefix16 else (if i<18 then UpperProfileCertificateData.prefix17 else UpperProfileCertificateData.prefix18)) else (if i<20 then UpperProfileCertificateData.prefix19 else (if i<21 then UpperProfileCertificateData.prefix20 else UpperProfileCertificateData.prefix21))))) else (if i<33 then (if i<27 then (if i<24 then (if i<23 then UpperProfileCertificateData.prefix22 else UpperProfileCertificateData.prefix23) else (if i<25 then UpperProfileCertificateData.prefix24 else (if i<26 then UpperProfileCertificateData.prefix25 else UpperProfileCertificateData.prefix26))) else (if i<30 then (if i<28 then UpperProfileCertificateData.prefix27 else (if i<29 then UpperProfileCertificateData.prefix28 else UpperProfileCertificateData.prefix29)) else (if i<31 then UpperProfileCertificateData.prefix30 else (if i<32 then UpperProfileCertificateData.prefix31 else UpperProfileCertificateData.prefix32)))) else (if i<39 then (if i<36 then (if i<34 then UpperProfileCertificateData.prefix33 else (if i<35 then UpperProfileCertificateData.prefix34 else UpperProfileCertificateData.prefix35)) else (if i<37 then UpperProfileCertificateData.prefix36 else (if i<38 then UpperProfileCertificateData.prefix37 else UpperProfileCertificateData.prefix38))) else (if i<42 then (if i<40 then UpperProfileCertificateData.prefix39 else (if i<41 then UpperProfileCertificateData.prefix40 else UpperProfileCertificateData.prefix41)) else (if i<43 then UpperProfileCertificateData.prefix42 else (if i<44 then UpperProfileCertificateData.prefix43 else UpperProfileCertificateData.prefix44)))))) else (if i<67 then (if i<56 then (if i<50 then (if i<47 then (if i<46 then UpperProfileCertificateData.prefix45 else UpperProfileCertificateData.prefix46) else (if i<48 then UpperProfileCertificateData.prefix47 else (if i<49 then UpperProfileCertificateData.prefix48 else UpperProfileCertificateData.prefix49))) else (if i<53 then (if i<51 then UpperProfileCertificateData.prefix50 else (if i<52 then UpperProfileCertificateData.prefix51 else UpperProfileCertificateData.prefix52)) else (if i<54 then UpperProfileCertificateData.prefix53 else (if i<55 then UpperProfileCertificateData.prefix54 else UpperProfileCertificateData.prefix55)))) else (if i<61 then (if i<58 then (if i<57 then UpperProfileCertificateData.prefix56 else UpperProfileCertificateData.prefix57) else (if i<59 then UpperProfileCertificateData.prefix58 else (if i<60 then UpperProfileCertificateData.prefix59 else UpperProfileCertificateData.prefix60))) else (if i<64 then (if i<62 then UpperProfileCertificateData.prefix61 else (if i<63 then UpperProfileCertificateData.prefix62 else UpperProfileCertificateData.prefix63)) else (if i<65 then UpperProfileCertificateData.prefix64 else (if i<66 then UpperProfileCertificateData.prefix65 else UpperProfileCertificateData.prefix66))))) else (if i<78 then (if i<72 then (if i<69 then (if i<68 then UpperProfileCertificateData.prefix67 else UpperProfileCertificateData.prefix68) else (if i<70 then UpperProfileCertificateData.prefix69 else (if i<71 then UpperProfileCertificateData.prefix70 else UpperProfileCertificateData.prefix71))) else (if i<75 then (if i<73 then UpperProfileCertificateData.prefix72 else (if i<74 then UpperProfileCertificateData.prefix73 else UpperProfileCertificateData.prefix74)) else (if i<76 then UpperProfileCertificateData.prefix75 else (if i<77 then UpperProfileCertificateData.prefix76 else UpperProfileCertificateData.prefix77)))) else (if i<84 then (if i<81 then (if i<79 then UpperProfileCertificateData.prefix78 else (if i<80 then UpperProfileCertificateData.prefix79 else UpperProfileCertificateData.prefix80)) else (if i<82 then UpperProfileCertificateData.prefix81 else (if i<83 then UpperProfileCertificateData.prefix82 else UpperProfileCertificateData.prefix83))) else (if i<87 then (if i<85 then UpperProfileCertificateData.prefix84 else (if i<86 then UpperProfileCertificateData.prefix85 else UpperProfileCertificateData.prefix86)) else (if i<88 then UpperProfileCertificateData.prefix87 else (if i<89 then UpperProfileCertificateData.prefix88 else UpperProfileCertificateData.prefix89))))))) else (if i<135 then (if i<112 then (if i<101 then (if i<95 then (if i<92 then (if i<91 then UpperProfileCertificateData.prefix90 else UpperProfileCertificateData.prefix91) else (if i<93 then UpperProfileCertificateData.prefix92 else (if i<94 then UpperProfileCertificateData.prefix93 else UpperProfileCertificateData.prefix94))) else (if i<98 then (if i<96 then UpperProfileCertificateData.prefix95 else (if i<97 then UpperProfileCertificateData.prefix96 else UpperProfileCertificateData.prefix97)) else (if i<99 then UpperProfileCertificateData.prefix98 else (if i<100 then UpperProfileCertificateData.prefix99 else UpperProfileCertificateData.prefix100)))) else (if i<106 then (if i<103 then (if i<102 then UpperProfileCertificateData.prefix101 else UpperProfileCertificateData.prefix102) else (if i<104 then UpperProfileCertificateData.prefix103 else (if i<105 then UpperProfileCertificateData.prefix104 else UpperProfileCertificateData.prefix105))) else (if i<109 then (if i<107 then UpperProfileCertificateData.prefix106 else (if i<108 then UpperProfileCertificateData.prefix107 else UpperProfileCertificateData.prefix108)) else (if i<110 then UpperProfileCertificateData.prefix109 else (if i<111 then UpperProfileCertificateData.prefix110 else UpperProfileCertificateData.prefix111))))) else (if i<123 then (if i<117 then (if i<114 then (if i<113 then UpperProfileCertificateData.prefix112 else UpperProfileCertificateData.prefix113) else (if i<115 then UpperProfileCertificateData.prefix114 else (if i<116 then UpperProfileCertificateData.prefix115 else UpperProfileCertificateData.prefix116))) else (if i<120 then (if i<118 then UpperProfileCertificateData.prefix117 else (if i<119 then UpperProfileCertificateData.prefix118 else UpperProfileCertificateData.prefix119)) else (if i<121 then UpperProfileCertificateData.prefix120 else (if i<122 then UpperProfileCertificateData.prefix121 else UpperProfileCertificateData.prefix122)))) else (if i<129 then (if i<126 then (if i<124 then UpperProfileCertificateData.prefix123 else (if i<125 then UpperProfileCertificateData.prefix124 else UpperProfileCertificateData.prefix125)) else (if i<127 then UpperProfileCertificateData.prefix126 else (if i<128 then UpperProfileCertificateData.prefix127 else UpperProfileCertificateData.prefix128))) else (if i<132 then (if i<130 then UpperProfileCertificateData.prefix129 else (if i<131 then UpperProfileCertificateData.prefix130 else UpperProfileCertificateData.prefix131)) else (if i<133 then UpperProfileCertificateData.prefix132 else (if i<134 then UpperProfileCertificateData.prefix133 else UpperProfileCertificateData.prefix134)))))) else (if i<157 then (if i<146 then (if i<140 then (if i<137 then (if i<136 then UpperProfileCertificateData.prefix135 else UpperProfileCertificateData.prefix136) else (if i<138 then UpperProfileCertificateData.prefix137 else (if i<139 then UpperProfileCertificateData.prefix138 else UpperProfileCertificateData.prefix139))) else (if i<143 then (if i<141 then UpperProfileCertificateData.prefix140 else (if i<142 then UpperProfileCertificateData.prefix141 else UpperProfileCertificateData.prefix142)) else (if i<144 then UpperProfileCertificateData.prefix143 else (if i<145 then UpperProfileCertificateData.prefix144 else UpperProfileCertificateData.prefix145)))) else (if i<151 then (if i<148 then (if i<147 then UpperProfileCertificateData.prefix146 else UpperProfileCertificateData.prefix147) else (if i<149 then UpperProfileCertificateData.prefix148 else (if i<150 then UpperProfileCertificateData.prefix149 else UpperProfileCertificateData.prefix150))) else (if i<154 then (if i<152 then UpperProfileCertificateData.prefix151 else (if i<153 then UpperProfileCertificateData.prefix152 else UpperProfileCertificateData.prefix153)) else (if i<155 then UpperProfileCertificateData.prefix154 else (if i<156 then UpperProfileCertificateData.prefix155 else UpperProfileCertificateData.prefix156))))) else (if i<168 then (if i<162 then (if i<159 then (if i<158 then UpperProfileCertificateData.prefix157 else UpperProfileCertificateData.prefix158) else (if i<160 then UpperProfileCertificateData.prefix159 else (if i<161 then UpperProfileCertificateData.prefix160 else UpperProfileCertificateData.prefix161))) else (if i<165 then (if i<163 then UpperProfileCertificateData.prefix162 else (if i<164 then UpperProfileCertificateData.prefix163 else UpperProfileCertificateData.prefix164)) else (if i<166 then UpperProfileCertificateData.prefix165 else (if i<167 then UpperProfileCertificateData.prefix166 else UpperProfileCertificateData.prefix167)))) else (if i<174 then (if i<171 then (if i<169 then UpperProfileCertificateData.prefix168 else (if i<170 then UpperProfileCertificateData.prefix169 else UpperProfileCertificateData.prefix170)) else (if i<172 then UpperProfileCertificateData.prefix171 else (if i<173 then UpperProfileCertificateData.prefix172 else UpperProfileCertificateData.prefix173))) else (if i<177 then (if i<175 then UpperProfileCertificateData.prefix174 else (if i<176 then UpperProfileCertificateData.prefix175 else UpperProfileCertificateData.prefix176)) else (if i<178 then UpperProfileCertificateData.prefix177 else (if i<179 then UpperProfileCertificateData.prefix178 else UpperProfileCertificateData.prefix179)))))))) else (if i<270 then (if i<225 then (if i<202 then (if i<191 then (if i<185 then (if i<182 then (if i<181 then UpperProfileCertificateData.prefix180 else UpperProfileCertificateData.prefix181) else (if i<183 then UpperProfileCertificateData.prefix182 else (if i<184 then UpperProfileCertificateData.prefix183 else UpperProfileCertificateData.prefix184))) else (if i<188 then (if i<186 then UpperProfileCertificateData.prefix185 else (if i<187 then UpperProfileCertificateData.prefix186 else UpperProfileCertificateData.prefix187)) else (if i<189 then UpperProfileCertificateData.prefix188 else (if i<190 then UpperProfileCertificateData.prefix189 else UpperProfileCertificateData.prefix190)))) else (if i<196 then (if i<193 then (if i<192 then UpperProfileCertificateData.prefix191 else UpperProfileCertificateData.prefix192) else (if i<194 then UpperProfileCertificateData.prefix193 else (if i<195 then UpperProfileCertificateData.prefix194 else UpperProfileCertificateData.prefix195))) else (if i<199 then (if i<197 then UpperProfileCertificateData.prefix196 else (if i<198 then UpperProfileCertificateData.prefix197 else UpperProfileCertificateData.prefix198)) else (if i<200 then UpperProfileCertificateData.prefix199 else (if i<201 then UpperProfileCertificateData.prefix200 else UpperProfileCertificateData.prefix201))))) else (if i<213 then (if i<207 then (if i<204 then (if i<203 then UpperProfileCertificateData.prefix202 else UpperProfileCertificateData.prefix203) else (if i<205 then UpperProfileCertificateData.prefix204 else (if i<206 then UpperProfileCertificateData.prefix205 else UpperProfileCertificateData.prefix206))) else (if i<210 then (if i<208 then UpperProfileCertificateData.prefix207 else (if i<209 then UpperProfileCertificateData.prefix208 else UpperProfileCertificateData.prefix209)) else (if i<211 then UpperProfileCertificateData.prefix210 else (if i<212 then UpperProfileCertificateData.prefix211 else UpperProfileCertificateData.prefix212)))) else (if i<219 then (if i<216 then (if i<214 then UpperProfileCertificateData.prefix213 else (if i<215 then UpperProfileCertificateData.prefix214 else UpperProfileCertificateData.prefix215)) else (if i<217 then UpperProfileCertificateData.prefix216 else (if i<218 then UpperProfileCertificateData.prefix217 else UpperProfileCertificateData.prefix218))) else (if i<222 then (if i<220 then UpperProfileCertificateData.prefix219 else (if i<221 then UpperProfileCertificateData.prefix220 else UpperProfileCertificateData.prefix221)) else (if i<223 then UpperProfileCertificateData.prefix222 else (if i<224 then UpperProfileCertificateData.prefix223 else UpperProfileCertificateData.prefix224)))))) else (if i<247 then (if i<236 then (if i<230 then (if i<227 then (if i<226 then UpperProfileCertificateData.prefix225 else UpperProfileCertificateData.prefix226) else (if i<228 then UpperProfileCertificateData.prefix227 else (if i<229 then UpperProfileCertificateData.prefix228 else UpperProfileCertificateData.prefix229))) else (if i<233 then (if i<231 then UpperProfileCertificateData.prefix230 else (if i<232 then UpperProfileCertificateData.prefix231 else UpperProfileCertificateData.prefix232)) else (if i<234 then UpperProfileCertificateData.prefix233 else (if i<235 then UpperProfileCertificateData.prefix234 else UpperProfileCertificateData.prefix235)))) else (if i<241 then (if i<238 then (if i<237 then UpperProfileCertificateData.prefix236 else UpperProfileCertificateData.prefix237) else (if i<239 then UpperProfileCertificateData.prefix238 else (if i<240 then UpperProfileCertificateData.prefix239 else UpperProfileCertificateData.prefix240))) else (if i<244 then (if i<242 then UpperProfileCertificateData.prefix241 else (if i<243 then UpperProfileCertificateData.prefix242 else UpperProfileCertificateData.prefix243)) else (if i<245 then UpperProfileCertificateData.prefix244 else (if i<246 then UpperProfileCertificateData.prefix245 else UpperProfileCertificateData.prefix246))))) else (if i<258 then (if i<252 then (if i<249 then (if i<248 then UpperProfileCertificateData.prefix247 else UpperProfileCertificateData.prefix248) else (if i<250 then UpperProfileCertificateData.prefix249 else (if i<251 then UpperProfileCertificateData.prefix250 else UpperProfileCertificateData.prefix251))) else (if i<255 then (if i<253 then UpperProfileCertificateData.prefix252 else (if i<254 then UpperProfileCertificateData.prefix253 else UpperProfileCertificateData.prefix254)) else (if i<256 then UpperProfileCertificateData.prefix255 else (if i<257 then UpperProfileCertificateData.prefix256 else UpperProfileCertificateData.prefix257)))) else (if i<264 then (if i<261 then (if i<259 then UpperProfileCertificateData.prefix258 else (if i<260 then UpperProfileCertificateData.prefix259 else UpperProfileCertificateData.prefix260)) else (if i<262 then UpperProfileCertificateData.prefix261 else (if i<263 then UpperProfileCertificateData.prefix262 else UpperProfileCertificateData.prefix263))) else (if i<267 then (if i<265 then UpperProfileCertificateData.prefix264 else (if i<266 then UpperProfileCertificateData.prefix265 else UpperProfileCertificateData.prefix266)) else (if i<268 then UpperProfileCertificateData.prefix267 else (if i<269 then UpperProfileCertificateData.prefix268 else UpperProfileCertificateData.prefix269))))))) else (if i<315 then (if i<292 then (if i<281 then (if i<275 then (if i<272 then (if i<271 then UpperProfileCertificateData.prefix270 else UpperProfileCertificateData.prefix271) else (if i<273 then UpperProfileCertificateData.prefix272 else (if i<274 then UpperProfileCertificateData.prefix273 else UpperProfileCertificateData.prefix274))) else (if i<278 then (if i<276 then UpperProfileCertificateData.prefix275 else (if i<277 then UpperProfileCertificateData.prefix276 else UpperProfileCertificateData.prefix277)) else (if i<279 then UpperProfileCertificateData.prefix278 else (if i<280 then UpperProfileCertificateData.prefix279 else UpperProfileCertificateData.prefix280)))) else (if i<286 then (if i<283 then (if i<282 then UpperProfileCertificateData.prefix281 else UpperProfileCertificateData.prefix282) else (if i<284 then UpperProfileCertificateData.prefix283 else (if i<285 then UpperProfileCertificateData.prefix284 else UpperProfileCertificateData.prefix285))) else (if i<289 then (if i<287 then UpperProfileCertificateData.prefix286 else (if i<288 then UpperProfileCertificateData.prefix287 else UpperProfileCertificateData.prefix288)) else (if i<290 then UpperProfileCertificateData.prefix289 else (if i<291 then UpperProfileCertificateData.prefix290 else UpperProfileCertificateData.prefix291))))) else (if i<303 then (if i<297 then (if i<294 then (if i<293 then UpperProfileCertificateData.prefix292 else UpperProfileCertificateData.prefix293) else (if i<295 then UpperProfileCertificateData.prefix294 else (if i<296 then UpperProfileCertificateData.prefix295 else UpperProfileCertificateData.prefix296))) else (if i<300 then (if i<298 then UpperProfileCertificateData.prefix297 else (if i<299 then UpperProfileCertificateData.prefix298 else UpperProfileCertificateData.prefix299)) else (if i<301 then UpperProfileCertificateData.prefix300 else (if i<302 then UpperProfileCertificateData.prefix301 else UpperProfileCertificateData.prefix302)))) else (if i<309 then (if i<306 then (if i<304 then UpperProfileCertificateData.prefix303 else (if i<305 then UpperProfileCertificateData.prefix304 else UpperProfileCertificateData.prefix305)) else (if i<307 then UpperProfileCertificateData.prefix306 else (if i<308 then UpperProfileCertificateData.prefix307 else UpperProfileCertificateData.prefix308))) else (if i<312 then (if i<310 then UpperProfileCertificateData.prefix309 else (if i<311 then UpperProfileCertificateData.prefix310 else UpperProfileCertificateData.prefix311)) else (if i<313 then UpperProfileCertificateData.prefix312 else (if i<314 then UpperProfileCertificateData.prefix313 else UpperProfileCertificateData.prefix314)))))) else (if i<337 then (if i<326 then (if i<320 then (if i<317 then (if i<316 then UpperProfileCertificateData.prefix315 else UpperProfileCertificateData.prefix316) else (if i<318 then UpperProfileCertificateData.prefix317 else (if i<319 then UpperProfileCertificateData.prefix318 else UpperProfileCertificateData.prefix319))) else (if i<323 then (if i<321 then UpperProfileCertificateData.prefix320 else (if i<322 then UpperProfileCertificateData.prefix321 else UpperProfileCertificateData.prefix322)) else (if i<324 then UpperProfileCertificateData.prefix323 else (if i<325 then UpperProfileCertificateData.prefix324 else UpperProfileCertificateData.prefix325)))) else (if i<331 then (if i<328 then (if i<327 then UpperProfileCertificateData.prefix326 else UpperProfileCertificateData.prefix327) else (if i<329 then UpperProfileCertificateData.prefix328 else (if i<330 then UpperProfileCertificateData.prefix329 else UpperProfileCertificateData.prefix330))) else (if i<334 then (if i<332 then UpperProfileCertificateData.prefix331 else (if i<333 then UpperProfileCertificateData.prefix332 else UpperProfileCertificateData.prefix333)) else (if i<335 then UpperProfileCertificateData.prefix334 else (if i<336 then UpperProfileCertificateData.prefix335 else UpperProfileCertificateData.prefix336))))) else (if i<348 then (if i<342 then (if i<339 then (if i<338 then UpperProfileCertificateData.prefix337 else UpperProfileCertificateData.prefix338) else (if i<340 then UpperProfileCertificateData.prefix339 else (if i<341 then UpperProfileCertificateData.prefix340 else UpperProfileCertificateData.prefix341))) else (if i<345 then (if i<343 then UpperProfileCertificateData.prefix342 else (if i<344 then UpperProfileCertificateData.prefix343 else UpperProfileCertificateData.prefix344)) else (if i<346 then UpperProfileCertificateData.prefix345 else (if i<347 then UpperProfileCertificateData.prefix346 else UpperProfileCertificateData.prefix347)))) else (if i<354 then (if i<351 then (if i<349 then UpperProfileCertificateData.prefix348 else (if i<350 then UpperProfileCertificateData.prefix349 else UpperProfileCertificateData.prefix350)) else (if i<352 then UpperProfileCertificateData.prefix351 else (if i<353 then UpperProfileCertificateData.prefix352 else UpperProfileCertificateData.prefix353))) else (if i<357 then (if i<355 then UpperProfileCertificateData.prefix354 else (if i<356 then UpperProfileCertificateData.prefix355 else UpperProfileCertificateData.prefix356)) else (if i<358 then UpperProfileCertificateData.prefix357 else (if i<359 then UpperProfileCertificateData.prefix358 else UpperProfileCertificateData.prefix359))))))))) else (if i<540 then (if i<450 then (if i<405 then (if i<382 then (if i<371 then (if i<365 then (if i<362 then (if i<361 then UpperProfileCertificateData.prefix360 else UpperProfileCertificateData.prefix361) else (if i<363 then UpperProfileCertificateData.prefix362 else (if i<364 then UpperProfileCertificateData.prefix363 else UpperProfileCertificateData.prefix364))) else (if i<368 then (if i<366 then UpperProfileCertificateData.prefix365 else (if i<367 then UpperProfileCertificateData.prefix366 else UpperProfileCertificateData.prefix367)) else (if i<369 then UpperProfileCertificateData.prefix368 else (if i<370 then UpperProfileCertificateData.prefix369 else UpperProfileCertificateData.prefix370)))) else (if i<376 then (if i<373 then (if i<372 then UpperProfileCertificateData.prefix371 else UpperProfileCertificateData.prefix372) else (if i<374 then UpperProfileCertificateData.prefix373 else (if i<375 then UpperProfileCertificateData.prefix374 else UpperProfileCertificateData.prefix375))) else (if i<379 then (if i<377 then UpperProfileCertificateData.prefix376 else (if i<378 then UpperProfileCertificateData.prefix377 else UpperProfileCertificateData.prefix378)) else (if i<380 then UpperProfileCertificateData.prefix379 else (if i<381 then UpperProfileCertificateData.prefix380 else UpperProfileCertificateData.prefix381))))) else (if i<393 then (if i<387 then (if i<384 then (if i<383 then UpperProfileCertificateData.prefix382 else UpperProfileCertificateData.prefix383) else (if i<385 then UpperProfileCertificateData.prefix384 else (if i<386 then UpperProfileCertificateData.prefix385 else UpperProfileCertificateData.prefix386))) else (if i<390 then (if i<388 then UpperProfileCertificateData.prefix387 else (if i<389 then UpperProfileCertificateData.prefix388 else UpperProfileCertificateData.prefix389)) else (if i<391 then UpperProfileCertificateData.prefix390 else (if i<392 then UpperProfileCertificateData.prefix391 else UpperProfileCertificateData.prefix392)))) else (if i<399 then (if i<396 then (if i<394 then UpperProfileCertificateData.prefix393 else (if i<395 then UpperProfileCertificateData.prefix394 else UpperProfileCertificateData.prefix395)) else (if i<397 then UpperProfileCertificateData.prefix396 else (if i<398 then UpperProfileCertificateData.prefix397 else UpperProfileCertificateData.prefix398))) else (if i<402 then (if i<400 then UpperProfileCertificateData.prefix399 else (if i<401 then UpperProfileCertificateData.prefix400 else UpperProfileCertificateData.prefix401)) else (if i<403 then UpperProfileCertificateData.prefix402 else (if i<404 then UpperProfileCertificateData.prefix403 else UpperProfileCertificateData.prefix404)))))) else (if i<427 then (if i<416 then (if i<410 then (if i<407 then (if i<406 then UpperProfileCertificateData.prefix405 else UpperProfileCertificateData.prefix406) else (if i<408 then UpperProfileCertificateData.prefix407 else (if i<409 then UpperProfileCertificateData.prefix408 else UpperProfileCertificateData.prefix409))) else (if i<413 then (if i<411 then UpperProfileCertificateData.prefix410 else (if i<412 then UpperProfileCertificateData.prefix411 else UpperProfileCertificateData.prefix412)) else (if i<414 then UpperProfileCertificateData.prefix413 else (if i<415 then UpperProfileCertificateData.prefix414 else UpperProfileCertificateData.prefix415)))) else (if i<421 then (if i<418 then (if i<417 then UpperProfileCertificateData.prefix416 else UpperProfileCertificateData.prefix417) else (if i<419 then UpperProfileCertificateData.prefix418 else (if i<420 then UpperProfileCertificateData.prefix419 else UpperProfileCertificateData.prefix420))) else (if i<424 then (if i<422 then UpperProfileCertificateData.prefix421 else (if i<423 then UpperProfileCertificateData.prefix422 else UpperProfileCertificateData.prefix423)) else (if i<425 then UpperProfileCertificateData.prefix424 else (if i<426 then UpperProfileCertificateData.prefix425 else UpperProfileCertificateData.prefix426))))) else (if i<438 then (if i<432 then (if i<429 then (if i<428 then UpperProfileCertificateData.prefix427 else UpperProfileCertificateData.prefix428) else (if i<430 then UpperProfileCertificateData.prefix429 else (if i<431 then UpperProfileCertificateData.prefix430 else UpperProfileCertificateData.prefix431))) else (if i<435 then (if i<433 then UpperProfileCertificateData.prefix432 else (if i<434 then UpperProfileCertificateData.prefix433 else UpperProfileCertificateData.prefix434)) else (if i<436 then UpperProfileCertificateData.prefix435 else (if i<437 then UpperProfileCertificateData.prefix436 else UpperProfileCertificateData.prefix437)))) else (if i<444 then (if i<441 then (if i<439 then UpperProfileCertificateData.prefix438 else (if i<440 then UpperProfileCertificateData.prefix439 else UpperProfileCertificateData.prefix440)) else (if i<442 then UpperProfileCertificateData.prefix441 else (if i<443 then UpperProfileCertificateData.prefix442 else UpperProfileCertificateData.prefix443))) else (if i<447 then (if i<445 then UpperProfileCertificateData.prefix444 else (if i<446 then UpperProfileCertificateData.prefix445 else UpperProfileCertificateData.prefix446)) else (if i<448 then UpperProfileCertificateData.prefix447 else (if i<449 then UpperProfileCertificateData.prefix448 else UpperProfileCertificateData.prefix449))))))) else (if i<495 then (if i<472 then (if i<461 then (if i<455 then (if i<452 then (if i<451 then UpperProfileCertificateData.prefix450 else UpperProfileCertificateData.prefix451) else (if i<453 then UpperProfileCertificateData.prefix452 else (if i<454 then UpperProfileCertificateData.prefix453 else UpperProfileCertificateData.prefix454))) else (if i<458 then (if i<456 then UpperProfileCertificateData.prefix455 else (if i<457 then UpperProfileCertificateData.prefix456 else UpperProfileCertificateData.prefix457)) else (if i<459 then UpperProfileCertificateData.prefix458 else (if i<460 then UpperProfileCertificateData.prefix459 else UpperProfileCertificateData.prefix460)))) else (if i<466 then (if i<463 then (if i<462 then UpperProfileCertificateData.prefix461 else UpperProfileCertificateData.prefix462) else (if i<464 then UpperProfileCertificateData.prefix463 else (if i<465 then UpperProfileCertificateData.prefix464 else UpperProfileCertificateData.prefix465))) else (if i<469 then (if i<467 then UpperProfileCertificateData.prefix466 else (if i<468 then UpperProfileCertificateData.prefix467 else UpperProfileCertificateData.prefix468)) else (if i<470 then UpperProfileCertificateData.prefix469 else (if i<471 then UpperProfileCertificateData.prefix470 else UpperProfileCertificateData.prefix471))))) else (if i<483 then (if i<477 then (if i<474 then (if i<473 then UpperProfileCertificateData.prefix472 else UpperProfileCertificateData.prefix473) else (if i<475 then UpperProfileCertificateData.prefix474 else (if i<476 then UpperProfileCertificateData.prefix475 else UpperProfileCertificateData.prefix476))) else (if i<480 then (if i<478 then UpperProfileCertificateData.prefix477 else (if i<479 then UpperProfileCertificateData.prefix478 else UpperProfileCertificateData.prefix479)) else (if i<481 then UpperProfileCertificateData.prefix480 else (if i<482 then UpperProfileCertificateData.prefix481 else UpperProfileCertificateData.prefix482)))) else (if i<489 then (if i<486 then (if i<484 then UpperProfileCertificateData.prefix483 else (if i<485 then UpperProfileCertificateData.prefix484 else UpperProfileCertificateData.prefix485)) else (if i<487 then UpperProfileCertificateData.prefix486 else (if i<488 then UpperProfileCertificateData.prefix487 else UpperProfileCertificateData.prefix488))) else (if i<492 then (if i<490 then UpperProfileCertificateData.prefix489 else (if i<491 then UpperProfileCertificateData.prefix490 else UpperProfileCertificateData.prefix491)) else (if i<493 then UpperProfileCertificateData.prefix492 else (if i<494 then UpperProfileCertificateData.prefix493 else UpperProfileCertificateData.prefix494)))))) else (if i<517 then (if i<506 then (if i<500 then (if i<497 then (if i<496 then UpperProfileCertificateData.prefix495 else UpperProfileCertificateData.prefix496) else (if i<498 then UpperProfileCertificateData.prefix497 else (if i<499 then UpperProfileCertificateData.prefix498 else UpperProfileCertificateData.prefix499))) else (if i<503 then (if i<501 then UpperProfileCertificateData.prefix500 else (if i<502 then UpperProfileCertificateData.prefix501 else UpperProfileCertificateData.prefix502)) else (if i<504 then UpperProfileCertificateData.prefix503 else (if i<505 then UpperProfileCertificateData.prefix504 else UpperProfileCertificateData.prefix505)))) else (if i<511 then (if i<508 then (if i<507 then UpperProfileCertificateData.prefix506 else UpperProfileCertificateData.prefix507) else (if i<509 then UpperProfileCertificateData.prefix508 else (if i<510 then UpperProfileCertificateData.prefix509 else UpperProfileCertificateData.prefix510))) else (if i<514 then (if i<512 then UpperProfileCertificateData.prefix511 else (if i<513 then UpperProfileCertificateData.prefix512 else UpperProfileCertificateData.prefix513)) else (if i<515 then UpperProfileCertificateData.prefix514 else (if i<516 then UpperProfileCertificateData.prefix515 else UpperProfileCertificateData.prefix516))))) else (if i<528 then (if i<522 then (if i<519 then (if i<518 then UpperProfileCertificateData.prefix517 else UpperProfileCertificateData.prefix518) else (if i<520 then UpperProfileCertificateData.prefix519 else (if i<521 then UpperProfileCertificateData.prefix520 else UpperProfileCertificateData.prefix521))) else (if i<525 then (if i<523 then UpperProfileCertificateData.prefix522 else (if i<524 then UpperProfileCertificateData.prefix523 else UpperProfileCertificateData.prefix524)) else (if i<526 then UpperProfileCertificateData.prefix525 else (if i<527 then UpperProfileCertificateData.prefix526 else UpperProfileCertificateData.prefix527)))) else (if i<534 then (if i<531 then (if i<529 then UpperProfileCertificateData.prefix528 else (if i<530 then UpperProfileCertificateData.prefix529 else UpperProfileCertificateData.prefix530)) else (if i<532 then UpperProfileCertificateData.prefix531 else (if i<533 then UpperProfileCertificateData.prefix532 else UpperProfileCertificateData.prefix533))) else (if i<537 then (if i<535 then UpperProfileCertificateData.prefix534 else (if i<536 then UpperProfileCertificateData.prefix535 else UpperProfileCertificateData.prefix536)) else (if i<538 then UpperProfileCertificateData.prefix537 else (if i<539 then UpperProfileCertificateData.prefix538 else UpperProfileCertificateData.prefix539)))))))) else (if i<630 then (if i<585 then (if i<562 then (if i<551 then (if i<545 then (if i<542 then (if i<541 then UpperProfileCertificateData.prefix540 else UpperProfileCertificateData.prefix541) else (if i<543 then UpperProfileCertificateData.prefix542 else (if i<544 then UpperProfileCertificateData.prefix543 else UpperProfileCertificateData.prefix544))) else (if i<548 then (if i<546 then UpperProfileCertificateData.prefix545 else (if i<547 then UpperProfileCertificateData.prefix546 else UpperProfileCertificateData.prefix547)) else (if i<549 then UpperProfileCertificateData.prefix548 else (if i<550 then UpperProfileCertificateData.prefix549 else UpperProfileCertificateData.prefix550)))) else (if i<556 then (if i<553 then (if i<552 then UpperProfileCertificateData.prefix551 else UpperProfileCertificateData.prefix552) else (if i<554 then UpperProfileCertificateData.prefix553 else (if i<555 then UpperProfileCertificateData.prefix554 else UpperProfileCertificateData.prefix555))) else (if i<559 then (if i<557 then UpperProfileCertificateData.prefix556 else (if i<558 then UpperProfileCertificateData.prefix557 else UpperProfileCertificateData.prefix558)) else (if i<560 then UpperProfileCertificateData.prefix559 else (if i<561 then UpperProfileCertificateData.prefix560 else UpperProfileCertificateData.prefix561))))) else (if i<573 then (if i<567 then (if i<564 then (if i<563 then UpperProfileCertificateData.prefix562 else UpperProfileCertificateData.prefix563) else (if i<565 then UpperProfileCertificateData.prefix564 else (if i<566 then UpperProfileCertificateData.prefix565 else UpperProfileCertificateData.prefix566))) else (if i<570 then (if i<568 then UpperProfileCertificateData.prefix567 else (if i<569 then UpperProfileCertificateData.prefix568 else UpperProfileCertificateData.prefix569)) else (if i<571 then UpperProfileCertificateData.prefix570 else (if i<572 then UpperProfileCertificateData.prefix571 else UpperProfileCertificateData.prefix572)))) else (if i<579 then (if i<576 then (if i<574 then UpperProfileCertificateData.prefix573 else (if i<575 then UpperProfileCertificateData.prefix574 else UpperProfileCertificateData.prefix575)) else (if i<577 then UpperProfileCertificateData.prefix576 else (if i<578 then UpperProfileCertificateData.prefix577 else UpperProfileCertificateData.prefix578))) else (if i<582 then (if i<580 then UpperProfileCertificateData.prefix579 else (if i<581 then UpperProfileCertificateData.prefix580 else UpperProfileCertificateData.prefix581)) else (if i<583 then UpperProfileCertificateData.prefix582 else (if i<584 then UpperProfileCertificateData.prefix583 else UpperProfileCertificateData.prefix584)))))) else (if i<607 then (if i<596 then (if i<590 then (if i<587 then (if i<586 then UpperProfileCertificateData.prefix585 else UpperProfileCertificateData.prefix586) else (if i<588 then UpperProfileCertificateData.prefix587 else (if i<589 then UpperProfileCertificateData.prefix588 else UpperProfileCertificateData.prefix589))) else (if i<593 then (if i<591 then UpperProfileCertificateData.prefix590 else (if i<592 then UpperProfileCertificateData.prefix591 else UpperProfileCertificateData.prefix592)) else (if i<594 then UpperProfileCertificateData.prefix593 else (if i<595 then UpperProfileCertificateData.prefix594 else UpperProfileCertificateData.prefix595)))) else (if i<601 then (if i<598 then (if i<597 then UpperProfileCertificateData.prefix596 else UpperProfileCertificateData.prefix597) else (if i<599 then UpperProfileCertificateData.prefix598 else (if i<600 then UpperProfileCertificateData.prefix599 else UpperProfileCertificateData.prefix600))) else (if i<604 then (if i<602 then UpperProfileCertificateData.prefix601 else (if i<603 then UpperProfileCertificateData.prefix602 else UpperProfileCertificateData.prefix603)) else (if i<605 then UpperProfileCertificateData.prefix604 else (if i<606 then UpperProfileCertificateData.prefix605 else UpperProfileCertificateData.prefix606))))) else (if i<618 then (if i<612 then (if i<609 then (if i<608 then UpperProfileCertificateData.prefix607 else UpperProfileCertificateData.prefix608) else (if i<610 then UpperProfileCertificateData.prefix609 else (if i<611 then UpperProfileCertificateData.prefix610 else UpperProfileCertificateData.prefix611))) else (if i<615 then (if i<613 then UpperProfileCertificateData.prefix612 else (if i<614 then UpperProfileCertificateData.prefix613 else UpperProfileCertificateData.prefix614)) else (if i<616 then UpperProfileCertificateData.prefix615 else (if i<617 then UpperProfileCertificateData.prefix616 else UpperProfileCertificateData.prefix617)))) else (if i<624 then (if i<621 then (if i<619 then UpperProfileCertificateData.prefix618 else (if i<620 then UpperProfileCertificateData.prefix619 else UpperProfileCertificateData.prefix620)) else (if i<622 then UpperProfileCertificateData.prefix621 else (if i<623 then UpperProfileCertificateData.prefix622 else UpperProfileCertificateData.prefix623))) else (if i<627 then (if i<625 then UpperProfileCertificateData.prefix624 else (if i<626 then UpperProfileCertificateData.prefix625 else UpperProfileCertificateData.prefix626)) else (if i<628 then UpperProfileCertificateData.prefix627 else (if i<629 then UpperProfileCertificateData.prefix628 else UpperProfileCertificateData.prefix629))))))) else (if i<675 then (if i<652 then (if i<641 then (if i<635 then (if i<632 then (if i<631 then UpperProfileCertificateData.prefix630 else UpperProfileCertificateData.prefix631) else (if i<633 then UpperProfileCertificateData.prefix632 else (if i<634 then UpperProfileCertificateData.prefix633 else UpperProfileCertificateData.prefix634))) else (if i<638 then (if i<636 then UpperProfileCertificateData.prefix635 else (if i<637 then UpperProfileCertificateData.prefix636 else UpperProfileCertificateData.prefix637)) else (if i<639 then UpperProfileCertificateData.prefix638 else (if i<640 then UpperProfileCertificateData.prefix639 else UpperProfileCertificateData.prefix640)))) else (if i<646 then (if i<643 then (if i<642 then UpperProfileCertificateData.prefix641 else UpperProfileCertificateData.prefix642) else (if i<644 then UpperProfileCertificateData.prefix643 else (if i<645 then UpperProfileCertificateData.prefix644 else UpperProfileCertificateData.prefix645))) else (if i<649 then (if i<647 then UpperProfileCertificateData.prefix646 else (if i<648 then UpperProfileCertificateData.prefix647 else UpperProfileCertificateData.prefix648)) else (if i<650 then UpperProfileCertificateData.prefix649 else (if i<651 then UpperProfileCertificateData.prefix650 else UpperProfileCertificateData.prefix651))))) else (if i<663 then (if i<657 then (if i<654 then (if i<653 then UpperProfileCertificateData.prefix652 else UpperProfileCertificateData.prefix653) else (if i<655 then UpperProfileCertificateData.prefix654 else (if i<656 then UpperProfileCertificateData.prefix655 else UpperProfileCertificateData.prefix656))) else (if i<660 then (if i<658 then UpperProfileCertificateData.prefix657 else (if i<659 then UpperProfileCertificateData.prefix658 else UpperProfileCertificateData.prefix659)) else (if i<661 then UpperProfileCertificateData.prefix660 else (if i<662 then UpperProfileCertificateData.prefix661 else UpperProfileCertificateData.prefix662)))) else (if i<669 then (if i<666 then (if i<664 then UpperProfileCertificateData.prefix663 else (if i<665 then UpperProfileCertificateData.prefix664 else UpperProfileCertificateData.prefix665)) else (if i<667 then UpperProfileCertificateData.prefix666 else (if i<668 then UpperProfileCertificateData.prefix667 else UpperProfileCertificateData.prefix668))) else (if i<672 then (if i<670 then UpperProfileCertificateData.prefix669 else (if i<671 then UpperProfileCertificateData.prefix670 else UpperProfileCertificateData.prefix671)) else (if i<673 then UpperProfileCertificateData.prefix672 else (if i<674 then UpperProfileCertificateData.prefix673 else UpperProfileCertificateData.prefix674)))))) else (if i<697 then (if i<686 then (if i<680 then (if i<677 then (if i<676 then UpperProfileCertificateData.prefix675 else UpperProfileCertificateData.prefix676) else (if i<678 then UpperProfileCertificateData.prefix677 else (if i<679 then UpperProfileCertificateData.prefix678 else UpperProfileCertificateData.prefix679))) else (if i<683 then (if i<681 then UpperProfileCertificateData.prefix680 else (if i<682 then UpperProfileCertificateData.prefix681 else UpperProfileCertificateData.prefix682)) else (if i<684 then UpperProfileCertificateData.prefix683 else (if i<685 then UpperProfileCertificateData.prefix684 else UpperProfileCertificateData.prefix685)))) else (if i<691 then (if i<688 then (if i<687 then UpperProfileCertificateData.prefix686 else UpperProfileCertificateData.prefix687) else (if i<689 then UpperProfileCertificateData.prefix688 else (if i<690 then UpperProfileCertificateData.prefix689 else UpperProfileCertificateData.prefix690))) else (if i<694 then (if i<692 then UpperProfileCertificateData.prefix691 else (if i<693 then UpperProfileCertificateData.prefix692 else UpperProfileCertificateData.prefix693)) else (if i<695 then UpperProfileCertificateData.prefix694 else (if i<696 then UpperProfileCertificateData.prefix695 else UpperProfileCertificateData.prefix696))))) else (if i<708 then (if i<702 then (if i<699 then (if i<698 then UpperProfileCertificateData.prefix697 else UpperProfileCertificateData.prefix698) else (if i<700 then UpperProfileCertificateData.prefix699 else (if i<701 then UpperProfileCertificateData.prefix700 else UpperProfileCertificateData.prefix701))) else (if i<705 then (if i<703 then UpperProfileCertificateData.prefix702 else (if i<704 then UpperProfileCertificateData.prefix703 else UpperProfileCertificateData.prefix704)) else (if i<706 then UpperProfileCertificateData.prefix705 else (if i<707 then UpperProfileCertificateData.prefix706 else UpperProfileCertificateData.prefix707)))) else (if i<714 then (if i<711 then (if i<709 then UpperProfileCertificateData.prefix708 else (if i<710 then UpperProfileCertificateData.prefix709 else UpperProfileCertificateData.prefix710)) else (if i<712 then UpperProfileCertificateData.prefix711 else (if i<713 then UpperProfileCertificateData.prefix712 else UpperProfileCertificateData.prefix713))) else (if i<717 then (if i<715 then UpperProfileCertificateData.prefix714 else (if i<716 then UpperProfileCertificateData.prefix715 else UpperProfileCertificateData.prefix716)) else (if i<718 then UpperProfileCertificateData.prefix717 else (if i<719 then UpperProfileCertificateData.prefix718 else UpperProfileCertificateData.prefix719))))))))))
def value (j : ℕ) : ℝ := (UpperProfileCertificateData.height j : ℝ)/scale
def coefficient (j : ℕ) : ℝ := value j-value (j+1)

def RowCertified (i : ℕ) : Prop :=
    increments (roundedInverse i) (rowPrefix i) 0 (prefixLength i) = true ∧
    rowPrefix i 0=0 ∧
    scale*forceEntry i (rowPrefix i)+scale*(scale/10000)+scale*(scale/100000)+
      (∑ j ∈ Finset.range 720, matrixEntry i (rowPrefix i) j*
        (UpperProfileCertificateData.height j-UpperProfileCertificateData.height (j+1)))
      ≤ scale*UpperProfileCertificateData.height i
private theorem rows0 (i : Fin 120) : RowCertified i.val := by
  fin_cases i
  · change RowCertified 0
    unfold RowCertified
    rw [show rowPrefix 0 = UpperProfileCertificateData.prefix0 by rfl]
    exact UpperProfileCertificateData.row0_certificate
  · change RowCertified 1
    unfold RowCertified
    rw [show rowPrefix 1 = UpperProfileCertificateData.prefix1 by rfl]
    exact UpperProfileCertificateData.row1_certificate
  · change RowCertified 2
    unfold RowCertified
    rw [show rowPrefix 2 = UpperProfileCertificateData.prefix2 by rfl]
    exact UpperProfileCertificateData.row2_certificate
  · change RowCertified 3
    unfold RowCertified
    rw [show rowPrefix 3 = UpperProfileCertificateData.prefix3 by rfl]
    exact UpperProfileCertificateData.row3_certificate
  · change RowCertified 4
    unfold RowCertified
    rw [show rowPrefix 4 = UpperProfileCertificateData.prefix4 by rfl]
    exact UpperProfileCertificateData.row4_certificate
  · change RowCertified 5
    unfold RowCertified
    rw [show rowPrefix 5 = UpperProfileCertificateData.prefix5 by rfl]
    exact UpperProfileCertificateData.row5_certificate
  · change RowCertified 6
    unfold RowCertified
    rw [show rowPrefix 6 = UpperProfileCertificateData.prefix6 by rfl]
    exact UpperProfileCertificateData.row6_certificate
  · change RowCertified 7
    unfold RowCertified
    rw [show rowPrefix 7 = UpperProfileCertificateData.prefix7 by rfl]
    exact UpperProfileCertificateData.row7_certificate
  · change RowCertified 8
    unfold RowCertified
    rw [show rowPrefix 8 = UpperProfileCertificateData.prefix8 by rfl]
    exact UpperProfileCertificateData.row8_certificate
  · change RowCertified 9
    unfold RowCertified
    rw [show rowPrefix 9 = UpperProfileCertificateData.prefix9 by rfl]
    exact UpperProfileCertificateData.row9_certificate
  · change RowCertified 10
    unfold RowCertified
    rw [show rowPrefix 10 = UpperProfileCertificateData.prefix10 by rfl]
    exact UpperProfileCertificateData.row10_certificate
  · change RowCertified 11
    unfold RowCertified
    rw [show rowPrefix 11 = UpperProfileCertificateData.prefix11 by rfl]
    exact UpperProfileCertificateData.row11_certificate
  · change RowCertified 12
    unfold RowCertified
    rw [show rowPrefix 12 = UpperProfileCertificateData.prefix12 by rfl]
    exact UpperProfileCertificateData.row12_certificate
  · change RowCertified 13
    unfold RowCertified
    rw [show rowPrefix 13 = UpperProfileCertificateData.prefix13 by rfl]
    exact UpperProfileCertificateData.row13_certificate
  · change RowCertified 14
    unfold RowCertified
    rw [show rowPrefix 14 = UpperProfileCertificateData.prefix14 by rfl]
    exact UpperProfileCertificateData.row14_certificate
  · change RowCertified 15
    unfold RowCertified
    rw [show rowPrefix 15 = UpperProfileCertificateData.prefix15 by rfl]
    exact UpperProfileCertificateData.row15_certificate
  · change RowCertified 16
    unfold RowCertified
    rw [show rowPrefix 16 = UpperProfileCertificateData.prefix16 by rfl]
    exact UpperProfileCertificateData.row16_certificate
  · change RowCertified 17
    unfold RowCertified
    rw [show rowPrefix 17 = UpperProfileCertificateData.prefix17 by rfl]
    exact UpperProfileCertificateData.row17_certificate
  · change RowCertified 18
    unfold RowCertified
    rw [show rowPrefix 18 = UpperProfileCertificateData.prefix18 by rfl]
    exact UpperProfileCertificateData.row18_certificate
  · change RowCertified 19
    unfold RowCertified
    rw [show rowPrefix 19 = UpperProfileCertificateData.prefix19 by rfl]
    exact UpperProfileCertificateData.row19_certificate
  · change RowCertified 20
    unfold RowCertified
    rw [show rowPrefix 20 = UpperProfileCertificateData.prefix20 by rfl]
    exact UpperProfileCertificateData.row20_certificate
  · change RowCertified 21
    unfold RowCertified
    rw [show rowPrefix 21 = UpperProfileCertificateData.prefix21 by rfl]
    exact UpperProfileCertificateData.row21_certificate
  · change RowCertified 22
    unfold RowCertified
    rw [show rowPrefix 22 = UpperProfileCertificateData.prefix22 by rfl]
    exact UpperProfileCertificateData.row22_certificate
  · change RowCertified 23
    unfold RowCertified
    rw [show rowPrefix 23 = UpperProfileCertificateData.prefix23 by rfl]
    exact UpperProfileCertificateData.row23_certificate
  · change RowCertified 24
    unfold RowCertified
    rw [show rowPrefix 24 = UpperProfileCertificateData.prefix24 by rfl]
    exact UpperProfileCertificateData.row24_certificate
  · change RowCertified 25
    unfold RowCertified
    rw [show rowPrefix 25 = UpperProfileCertificateData.prefix25 by rfl]
    exact UpperProfileCertificateData.row25_certificate
  · change RowCertified 26
    unfold RowCertified
    rw [show rowPrefix 26 = UpperProfileCertificateData.prefix26 by rfl]
    exact UpperProfileCertificateData.row26_certificate
  · change RowCertified 27
    unfold RowCertified
    rw [show rowPrefix 27 = UpperProfileCertificateData.prefix27 by rfl]
    exact UpperProfileCertificateData.row27_certificate
  · change RowCertified 28
    unfold RowCertified
    rw [show rowPrefix 28 = UpperProfileCertificateData.prefix28 by rfl]
    exact UpperProfileCertificateData.row28_certificate
  · change RowCertified 29
    unfold RowCertified
    rw [show rowPrefix 29 = UpperProfileCertificateData.prefix29 by rfl]
    exact UpperProfileCertificateData.row29_certificate
  · change RowCertified 30
    unfold RowCertified
    rw [show rowPrefix 30 = UpperProfileCertificateData.prefix30 by rfl]
    exact UpperProfileCertificateData.row30_certificate
  · change RowCertified 31
    unfold RowCertified
    rw [show rowPrefix 31 = UpperProfileCertificateData.prefix31 by rfl]
    exact UpperProfileCertificateData.row31_certificate
  · change RowCertified 32
    unfold RowCertified
    rw [show rowPrefix 32 = UpperProfileCertificateData.prefix32 by rfl]
    exact UpperProfileCertificateData.row32_certificate
  · change RowCertified 33
    unfold RowCertified
    rw [show rowPrefix 33 = UpperProfileCertificateData.prefix33 by rfl]
    exact UpperProfileCertificateData.row33_certificate
  · change RowCertified 34
    unfold RowCertified
    rw [show rowPrefix 34 = UpperProfileCertificateData.prefix34 by rfl]
    exact UpperProfileCertificateData.row34_certificate
  · change RowCertified 35
    unfold RowCertified
    rw [show rowPrefix 35 = UpperProfileCertificateData.prefix35 by rfl]
    exact UpperProfileCertificateData.row35_certificate
  · change RowCertified 36
    unfold RowCertified
    rw [show rowPrefix 36 = UpperProfileCertificateData.prefix36 by rfl]
    exact UpperProfileCertificateData.row36_certificate
  · change RowCertified 37
    unfold RowCertified
    rw [show rowPrefix 37 = UpperProfileCertificateData.prefix37 by rfl]
    exact UpperProfileCertificateData.row37_certificate
  · change RowCertified 38
    unfold RowCertified
    rw [show rowPrefix 38 = UpperProfileCertificateData.prefix38 by rfl]
    exact UpperProfileCertificateData.row38_certificate
  · change RowCertified 39
    unfold RowCertified
    rw [show rowPrefix 39 = UpperProfileCertificateData.prefix39 by rfl]
    exact UpperProfileCertificateData.row39_certificate
  · change RowCertified 40
    unfold RowCertified
    rw [show rowPrefix 40 = UpperProfileCertificateData.prefix40 by rfl]
    exact UpperProfileCertificateData.row40_certificate
  · change RowCertified 41
    unfold RowCertified
    rw [show rowPrefix 41 = UpperProfileCertificateData.prefix41 by rfl]
    exact UpperProfileCertificateData.row41_certificate
  · change RowCertified 42
    unfold RowCertified
    rw [show rowPrefix 42 = UpperProfileCertificateData.prefix42 by rfl]
    exact UpperProfileCertificateData.row42_certificate
  · change RowCertified 43
    unfold RowCertified
    rw [show rowPrefix 43 = UpperProfileCertificateData.prefix43 by rfl]
    exact UpperProfileCertificateData.row43_certificate
  · change RowCertified 44
    unfold RowCertified
    rw [show rowPrefix 44 = UpperProfileCertificateData.prefix44 by rfl]
    exact UpperProfileCertificateData.row44_certificate
  · change RowCertified 45
    unfold RowCertified
    rw [show rowPrefix 45 = UpperProfileCertificateData.prefix45 by rfl]
    exact UpperProfileCertificateData.row45_certificate
  · change RowCertified 46
    unfold RowCertified
    rw [show rowPrefix 46 = UpperProfileCertificateData.prefix46 by rfl]
    exact UpperProfileCertificateData.row46_certificate
  · change RowCertified 47
    unfold RowCertified
    rw [show rowPrefix 47 = UpperProfileCertificateData.prefix47 by rfl]
    exact UpperProfileCertificateData.row47_certificate
  · change RowCertified 48
    unfold RowCertified
    rw [show rowPrefix 48 = UpperProfileCertificateData.prefix48 by rfl]
    exact UpperProfileCertificateData.row48_certificate
  · change RowCertified 49
    unfold RowCertified
    rw [show rowPrefix 49 = UpperProfileCertificateData.prefix49 by rfl]
    exact UpperProfileCertificateData.row49_certificate
  · change RowCertified 50
    unfold RowCertified
    rw [show rowPrefix 50 = UpperProfileCertificateData.prefix50 by rfl]
    exact UpperProfileCertificateData.row50_certificate
  · change RowCertified 51
    unfold RowCertified
    rw [show rowPrefix 51 = UpperProfileCertificateData.prefix51 by rfl]
    exact UpperProfileCertificateData.row51_certificate
  · change RowCertified 52
    unfold RowCertified
    rw [show rowPrefix 52 = UpperProfileCertificateData.prefix52 by rfl]
    exact UpperProfileCertificateData.row52_certificate
  · change RowCertified 53
    unfold RowCertified
    rw [show rowPrefix 53 = UpperProfileCertificateData.prefix53 by rfl]
    exact UpperProfileCertificateData.row53_certificate
  · change RowCertified 54
    unfold RowCertified
    rw [show rowPrefix 54 = UpperProfileCertificateData.prefix54 by rfl]
    exact UpperProfileCertificateData.row54_certificate
  · change RowCertified 55
    unfold RowCertified
    rw [show rowPrefix 55 = UpperProfileCertificateData.prefix55 by rfl]
    exact UpperProfileCertificateData.row55_certificate
  · change RowCertified 56
    unfold RowCertified
    rw [show rowPrefix 56 = UpperProfileCertificateData.prefix56 by rfl]
    exact UpperProfileCertificateData.row56_certificate
  · change RowCertified 57
    unfold RowCertified
    rw [show rowPrefix 57 = UpperProfileCertificateData.prefix57 by rfl]
    exact UpperProfileCertificateData.row57_certificate
  · change RowCertified 58
    unfold RowCertified
    rw [show rowPrefix 58 = UpperProfileCertificateData.prefix58 by rfl]
    exact UpperProfileCertificateData.row58_certificate
  · change RowCertified 59
    unfold RowCertified
    rw [show rowPrefix 59 = UpperProfileCertificateData.prefix59 by rfl]
    exact UpperProfileCertificateData.row59_certificate
  · change RowCertified 60
    unfold RowCertified
    rw [show rowPrefix 60 = UpperProfileCertificateData.prefix60 by rfl]
    exact UpperProfileCertificateData.row60_certificate
  · change RowCertified 61
    unfold RowCertified
    rw [show rowPrefix 61 = UpperProfileCertificateData.prefix61 by rfl]
    exact UpperProfileCertificateData.row61_certificate
  · change RowCertified 62
    unfold RowCertified
    rw [show rowPrefix 62 = UpperProfileCertificateData.prefix62 by rfl]
    exact UpperProfileCertificateData.row62_certificate
  · change RowCertified 63
    unfold RowCertified
    rw [show rowPrefix 63 = UpperProfileCertificateData.prefix63 by rfl]
    exact UpperProfileCertificateData.row63_certificate
  · change RowCertified 64
    unfold RowCertified
    rw [show rowPrefix 64 = UpperProfileCertificateData.prefix64 by rfl]
    exact UpperProfileCertificateData.row64_certificate
  · change RowCertified 65
    unfold RowCertified
    rw [show rowPrefix 65 = UpperProfileCertificateData.prefix65 by rfl]
    exact UpperProfileCertificateData.row65_certificate
  · change RowCertified 66
    unfold RowCertified
    rw [show rowPrefix 66 = UpperProfileCertificateData.prefix66 by rfl]
    exact UpperProfileCertificateData.row66_certificate
  · change RowCertified 67
    unfold RowCertified
    rw [show rowPrefix 67 = UpperProfileCertificateData.prefix67 by rfl]
    exact UpperProfileCertificateData.row67_certificate
  · change RowCertified 68
    unfold RowCertified
    rw [show rowPrefix 68 = UpperProfileCertificateData.prefix68 by rfl]
    exact UpperProfileCertificateData.row68_certificate
  · change RowCertified 69
    unfold RowCertified
    rw [show rowPrefix 69 = UpperProfileCertificateData.prefix69 by rfl]
    exact UpperProfileCertificateData.row69_certificate
  · change RowCertified 70
    unfold RowCertified
    rw [show rowPrefix 70 = UpperProfileCertificateData.prefix70 by rfl]
    exact UpperProfileCertificateData.row70_certificate
  · change RowCertified 71
    unfold RowCertified
    rw [show rowPrefix 71 = UpperProfileCertificateData.prefix71 by rfl]
    exact UpperProfileCertificateData.row71_certificate
  · change RowCertified 72
    unfold RowCertified
    rw [show rowPrefix 72 = UpperProfileCertificateData.prefix72 by rfl]
    exact UpperProfileCertificateData.row72_certificate
  · change RowCertified 73
    unfold RowCertified
    rw [show rowPrefix 73 = UpperProfileCertificateData.prefix73 by rfl]
    exact UpperProfileCertificateData.row73_certificate
  · change RowCertified 74
    unfold RowCertified
    rw [show rowPrefix 74 = UpperProfileCertificateData.prefix74 by rfl]
    exact UpperProfileCertificateData.row74_certificate
  · change RowCertified 75
    unfold RowCertified
    rw [show rowPrefix 75 = UpperProfileCertificateData.prefix75 by rfl]
    exact UpperProfileCertificateData.row75_certificate
  · change RowCertified 76
    unfold RowCertified
    rw [show rowPrefix 76 = UpperProfileCertificateData.prefix76 by rfl]
    exact UpperProfileCertificateData.row76_certificate
  · change RowCertified 77
    unfold RowCertified
    rw [show rowPrefix 77 = UpperProfileCertificateData.prefix77 by rfl]
    exact UpperProfileCertificateData.row77_certificate
  · change RowCertified 78
    unfold RowCertified
    rw [show rowPrefix 78 = UpperProfileCertificateData.prefix78 by rfl]
    exact UpperProfileCertificateData.row78_certificate
  · change RowCertified 79
    unfold RowCertified
    rw [show rowPrefix 79 = UpperProfileCertificateData.prefix79 by rfl]
    exact UpperProfileCertificateData.row79_certificate
  · change RowCertified 80
    unfold RowCertified
    rw [show rowPrefix 80 = UpperProfileCertificateData.prefix80 by rfl]
    exact UpperProfileCertificateData.row80_certificate
  · change RowCertified 81
    unfold RowCertified
    rw [show rowPrefix 81 = UpperProfileCertificateData.prefix81 by rfl]
    exact UpperProfileCertificateData.row81_certificate
  · change RowCertified 82
    unfold RowCertified
    rw [show rowPrefix 82 = UpperProfileCertificateData.prefix82 by rfl]
    exact UpperProfileCertificateData.row82_certificate
  · change RowCertified 83
    unfold RowCertified
    rw [show rowPrefix 83 = UpperProfileCertificateData.prefix83 by rfl]
    exact UpperProfileCertificateData.row83_certificate
  · change RowCertified 84
    unfold RowCertified
    rw [show rowPrefix 84 = UpperProfileCertificateData.prefix84 by rfl]
    exact UpperProfileCertificateData.row84_certificate
  · change RowCertified 85
    unfold RowCertified
    rw [show rowPrefix 85 = UpperProfileCertificateData.prefix85 by rfl]
    exact UpperProfileCertificateData.row85_certificate
  · change RowCertified 86
    unfold RowCertified
    rw [show rowPrefix 86 = UpperProfileCertificateData.prefix86 by rfl]
    exact UpperProfileCertificateData.row86_certificate
  · change RowCertified 87
    unfold RowCertified
    rw [show rowPrefix 87 = UpperProfileCertificateData.prefix87 by rfl]
    exact UpperProfileCertificateData.row87_certificate
  · change RowCertified 88
    unfold RowCertified
    rw [show rowPrefix 88 = UpperProfileCertificateData.prefix88 by rfl]
    exact UpperProfileCertificateData.row88_certificate
  · change RowCertified 89
    unfold RowCertified
    rw [show rowPrefix 89 = UpperProfileCertificateData.prefix89 by rfl]
    exact UpperProfileCertificateData.row89_certificate
  · change RowCertified 90
    unfold RowCertified
    rw [show rowPrefix 90 = UpperProfileCertificateData.prefix90 by rfl]
    exact UpperProfileCertificateData.row90_certificate
  · change RowCertified 91
    unfold RowCertified
    rw [show rowPrefix 91 = UpperProfileCertificateData.prefix91 by rfl]
    exact UpperProfileCertificateData.row91_certificate
  · change RowCertified 92
    unfold RowCertified
    rw [show rowPrefix 92 = UpperProfileCertificateData.prefix92 by rfl]
    exact UpperProfileCertificateData.row92_certificate
  · change RowCertified 93
    unfold RowCertified
    rw [show rowPrefix 93 = UpperProfileCertificateData.prefix93 by rfl]
    exact UpperProfileCertificateData.row93_certificate
  · change RowCertified 94
    unfold RowCertified
    rw [show rowPrefix 94 = UpperProfileCertificateData.prefix94 by rfl]
    exact UpperProfileCertificateData.row94_certificate
  · change RowCertified 95
    unfold RowCertified
    rw [show rowPrefix 95 = UpperProfileCertificateData.prefix95 by rfl]
    exact UpperProfileCertificateData.row95_certificate
  · change RowCertified 96
    unfold RowCertified
    rw [show rowPrefix 96 = UpperProfileCertificateData.prefix96 by rfl]
    exact UpperProfileCertificateData.row96_certificate
  · change RowCertified 97
    unfold RowCertified
    rw [show rowPrefix 97 = UpperProfileCertificateData.prefix97 by rfl]
    exact UpperProfileCertificateData.row97_certificate
  · change RowCertified 98
    unfold RowCertified
    rw [show rowPrefix 98 = UpperProfileCertificateData.prefix98 by rfl]
    exact UpperProfileCertificateData.row98_certificate
  · change RowCertified 99
    unfold RowCertified
    rw [show rowPrefix 99 = UpperProfileCertificateData.prefix99 by rfl]
    exact UpperProfileCertificateData.row99_certificate
  · change RowCertified 100
    unfold RowCertified
    rw [show rowPrefix 100 = UpperProfileCertificateData.prefix100 by rfl]
    exact UpperProfileCertificateData.row100_certificate
  · change RowCertified 101
    unfold RowCertified
    rw [show rowPrefix 101 = UpperProfileCertificateData.prefix101 by rfl]
    exact UpperProfileCertificateData.row101_certificate
  · change RowCertified 102
    unfold RowCertified
    rw [show rowPrefix 102 = UpperProfileCertificateData.prefix102 by rfl]
    exact UpperProfileCertificateData.row102_certificate
  · change RowCertified 103
    unfold RowCertified
    rw [show rowPrefix 103 = UpperProfileCertificateData.prefix103 by rfl]
    exact UpperProfileCertificateData.row103_certificate
  · change RowCertified 104
    unfold RowCertified
    rw [show rowPrefix 104 = UpperProfileCertificateData.prefix104 by rfl]
    exact UpperProfileCertificateData.row104_certificate
  · change RowCertified 105
    unfold RowCertified
    rw [show rowPrefix 105 = UpperProfileCertificateData.prefix105 by rfl]
    exact UpperProfileCertificateData.row105_certificate
  · change RowCertified 106
    unfold RowCertified
    rw [show rowPrefix 106 = UpperProfileCertificateData.prefix106 by rfl]
    exact UpperProfileCertificateData.row106_certificate
  · change RowCertified 107
    unfold RowCertified
    rw [show rowPrefix 107 = UpperProfileCertificateData.prefix107 by rfl]
    exact UpperProfileCertificateData.row107_certificate
  · change RowCertified 108
    unfold RowCertified
    rw [show rowPrefix 108 = UpperProfileCertificateData.prefix108 by rfl]
    exact UpperProfileCertificateData.row108_certificate
  · change RowCertified 109
    unfold RowCertified
    rw [show rowPrefix 109 = UpperProfileCertificateData.prefix109 by rfl]
    exact UpperProfileCertificateData.row109_certificate
  · change RowCertified 110
    unfold RowCertified
    rw [show rowPrefix 110 = UpperProfileCertificateData.prefix110 by rfl]
    exact UpperProfileCertificateData.row110_certificate
  · change RowCertified 111
    unfold RowCertified
    rw [show rowPrefix 111 = UpperProfileCertificateData.prefix111 by rfl]
    exact UpperProfileCertificateData.row111_certificate
  · change RowCertified 112
    unfold RowCertified
    rw [show rowPrefix 112 = UpperProfileCertificateData.prefix112 by rfl]
    exact UpperProfileCertificateData.row112_certificate
  · change RowCertified 113
    unfold RowCertified
    rw [show rowPrefix 113 = UpperProfileCertificateData.prefix113 by rfl]
    exact UpperProfileCertificateData.row113_certificate
  · change RowCertified 114
    unfold RowCertified
    rw [show rowPrefix 114 = UpperProfileCertificateData.prefix114 by rfl]
    exact UpperProfileCertificateData.row114_certificate
  · change RowCertified 115
    unfold RowCertified
    rw [show rowPrefix 115 = UpperProfileCertificateData.prefix115 by rfl]
    exact UpperProfileCertificateData.row115_certificate
  · change RowCertified 116
    unfold RowCertified
    rw [show rowPrefix 116 = UpperProfileCertificateData.prefix116 by rfl]
    exact UpperProfileCertificateData.row116_certificate
  · change RowCertified 117
    unfold RowCertified
    rw [show rowPrefix 117 = UpperProfileCertificateData.prefix117 by rfl]
    exact UpperProfileCertificateData.row117_certificate
  · change RowCertified 118
    unfold RowCertified
    rw [show rowPrefix 118 = UpperProfileCertificateData.prefix118 by rfl]
    exact UpperProfileCertificateData.row118_certificate
  · change RowCertified 119
    unfold RowCertified
    rw [show rowPrefix 119 = UpperProfileCertificateData.prefix119 by rfl]
    exact UpperProfileCertificateData.row119_certificate
run_cmd Lean.logInfo "FINER REAL INTERFACE: completed rows 0 through 119"
private theorem rows1 (i : Fin 120) : RowCertified (i.val+120) := by
  fin_cases i
  · change RowCertified 120
    unfold RowCertified
    rw [show rowPrefix 120 = UpperProfileCertificateData.prefix120 by rfl]
    exact UpperProfileCertificateData.row120_certificate
  · change RowCertified 121
    unfold RowCertified
    rw [show rowPrefix 121 = UpperProfileCertificateData.prefix121 by rfl]
    exact UpperProfileCertificateData.row121_certificate
  · change RowCertified 122
    unfold RowCertified
    rw [show rowPrefix 122 = UpperProfileCertificateData.prefix122 by rfl]
    exact UpperProfileCertificateData.row122_certificate
  · change RowCertified 123
    unfold RowCertified
    rw [show rowPrefix 123 = UpperProfileCertificateData.prefix123 by rfl]
    exact UpperProfileCertificateData.row123_certificate
  · change RowCertified 124
    unfold RowCertified
    rw [show rowPrefix 124 = UpperProfileCertificateData.prefix124 by rfl]
    exact UpperProfileCertificateData.row124_certificate
  · change RowCertified 125
    unfold RowCertified
    rw [show rowPrefix 125 = UpperProfileCertificateData.prefix125 by rfl]
    exact UpperProfileCertificateData.row125_certificate
  · change RowCertified 126
    unfold RowCertified
    rw [show rowPrefix 126 = UpperProfileCertificateData.prefix126 by rfl]
    exact UpperProfileCertificateData.row126_certificate
  · change RowCertified 127
    unfold RowCertified
    rw [show rowPrefix 127 = UpperProfileCertificateData.prefix127 by rfl]
    exact UpperProfileCertificateData.row127_certificate
  · change RowCertified 128
    unfold RowCertified
    rw [show rowPrefix 128 = UpperProfileCertificateData.prefix128 by rfl]
    exact UpperProfileCertificateData.row128_certificate
  · change RowCertified 129
    unfold RowCertified
    rw [show rowPrefix 129 = UpperProfileCertificateData.prefix129 by rfl]
    exact UpperProfileCertificateData.row129_certificate
  · change RowCertified 130
    unfold RowCertified
    rw [show rowPrefix 130 = UpperProfileCertificateData.prefix130 by rfl]
    exact UpperProfileCertificateData.row130_certificate
  · change RowCertified 131
    unfold RowCertified
    rw [show rowPrefix 131 = UpperProfileCertificateData.prefix131 by rfl]
    exact UpperProfileCertificateData.row131_certificate
  · change RowCertified 132
    unfold RowCertified
    rw [show rowPrefix 132 = UpperProfileCertificateData.prefix132 by rfl]
    exact UpperProfileCertificateData.row132_certificate
  · change RowCertified 133
    unfold RowCertified
    rw [show rowPrefix 133 = UpperProfileCertificateData.prefix133 by rfl]
    exact UpperProfileCertificateData.row133_certificate
  · change RowCertified 134
    unfold RowCertified
    rw [show rowPrefix 134 = UpperProfileCertificateData.prefix134 by rfl]
    exact UpperProfileCertificateData.row134_certificate
  · change RowCertified 135
    unfold RowCertified
    rw [show rowPrefix 135 = UpperProfileCertificateData.prefix135 by rfl]
    exact UpperProfileCertificateData.row135_certificate
  · change RowCertified 136
    unfold RowCertified
    rw [show rowPrefix 136 = UpperProfileCertificateData.prefix136 by rfl]
    exact UpperProfileCertificateData.row136_certificate
  · change RowCertified 137
    unfold RowCertified
    rw [show rowPrefix 137 = UpperProfileCertificateData.prefix137 by rfl]
    exact UpperProfileCertificateData.row137_certificate
  · change RowCertified 138
    unfold RowCertified
    rw [show rowPrefix 138 = UpperProfileCertificateData.prefix138 by rfl]
    exact UpperProfileCertificateData.row138_certificate
  · change RowCertified 139
    unfold RowCertified
    rw [show rowPrefix 139 = UpperProfileCertificateData.prefix139 by rfl]
    exact UpperProfileCertificateData.row139_certificate
  · change RowCertified 140
    unfold RowCertified
    rw [show rowPrefix 140 = UpperProfileCertificateData.prefix140 by rfl]
    exact UpperProfileCertificateData.row140_certificate
  · change RowCertified 141
    unfold RowCertified
    rw [show rowPrefix 141 = UpperProfileCertificateData.prefix141 by rfl]
    exact UpperProfileCertificateData.row141_certificate
  · change RowCertified 142
    unfold RowCertified
    rw [show rowPrefix 142 = UpperProfileCertificateData.prefix142 by rfl]
    exact UpperProfileCertificateData.row142_certificate
  · change RowCertified 143
    unfold RowCertified
    rw [show rowPrefix 143 = UpperProfileCertificateData.prefix143 by rfl]
    exact UpperProfileCertificateData.row143_certificate
  · change RowCertified 144
    unfold RowCertified
    rw [show rowPrefix 144 = UpperProfileCertificateData.prefix144 by rfl]
    exact UpperProfileCertificateData.row144_certificate
  · change RowCertified 145
    unfold RowCertified
    rw [show rowPrefix 145 = UpperProfileCertificateData.prefix145 by rfl]
    exact UpperProfileCertificateData.row145_certificate
  · change RowCertified 146
    unfold RowCertified
    rw [show rowPrefix 146 = UpperProfileCertificateData.prefix146 by rfl]
    exact UpperProfileCertificateData.row146_certificate
  · change RowCertified 147
    unfold RowCertified
    rw [show rowPrefix 147 = UpperProfileCertificateData.prefix147 by rfl]
    exact UpperProfileCertificateData.row147_certificate
  · change RowCertified 148
    unfold RowCertified
    rw [show rowPrefix 148 = UpperProfileCertificateData.prefix148 by rfl]
    exact UpperProfileCertificateData.row148_certificate
  · change RowCertified 149
    unfold RowCertified
    rw [show rowPrefix 149 = UpperProfileCertificateData.prefix149 by rfl]
    exact UpperProfileCertificateData.row149_certificate
  · change RowCertified 150
    unfold RowCertified
    rw [show rowPrefix 150 = UpperProfileCertificateData.prefix150 by rfl]
    exact UpperProfileCertificateData.row150_certificate
  · change RowCertified 151
    unfold RowCertified
    rw [show rowPrefix 151 = UpperProfileCertificateData.prefix151 by rfl]
    exact UpperProfileCertificateData.row151_certificate
  · change RowCertified 152
    unfold RowCertified
    rw [show rowPrefix 152 = UpperProfileCertificateData.prefix152 by rfl]
    exact UpperProfileCertificateData.row152_certificate
  · change RowCertified 153
    unfold RowCertified
    rw [show rowPrefix 153 = UpperProfileCertificateData.prefix153 by rfl]
    exact UpperProfileCertificateData.row153_certificate
  · change RowCertified 154
    unfold RowCertified
    rw [show rowPrefix 154 = UpperProfileCertificateData.prefix154 by rfl]
    exact UpperProfileCertificateData.row154_certificate
  · change RowCertified 155
    unfold RowCertified
    rw [show rowPrefix 155 = UpperProfileCertificateData.prefix155 by rfl]
    exact UpperProfileCertificateData.row155_certificate
  · change RowCertified 156
    unfold RowCertified
    rw [show rowPrefix 156 = UpperProfileCertificateData.prefix156 by rfl]
    exact UpperProfileCertificateData.row156_certificate
  · change RowCertified 157
    unfold RowCertified
    rw [show rowPrefix 157 = UpperProfileCertificateData.prefix157 by rfl]
    exact UpperProfileCertificateData.row157_certificate
  · change RowCertified 158
    unfold RowCertified
    rw [show rowPrefix 158 = UpperProfileCertificateData.prefix158 by rfl]
    exact UpperProfileCertificateData.row158_certificate
  · change RowCertified 159
    unfold RowCertified
    rw [show rowPrefix 159 = UpperProfileCertificateData.prefix159 by rfl]
    exact UpperProfileCertificateData.row159_certificate
  · change RowCertified 160
    unfold RowCertified
    rw [show rowPrefix 160 = UpperProfileCertificateData.prefix160 by rfl]
    exact UpperProfileCertificateData.row160_certificate
  · change RowCertified 161
    unfold RowCertified
    rw [show rowPrefix 161 = UpperProfileCertificateData.prefix161 by rfl]
    exact UpperProfileCertificateData.row161_certificate
  · change RowCertified 162
    unfold RowCertified
    rw [show rowPrefix 162 = UpperProfileCertificateData.prefix162 by rfl]
    exact UpperProfileCertificateData.row162_certificate
  · change RowCertified 163
    unfold RowCertified
    rw [show rowPrefix 163 = UpperProfileCertificateData.prefix163 by rfl]
    exact UpperProfileCertificateData.row163_certificate
  · change RowCertified 164
    unfold RowCertified
    rw [show rowPrefix 164 = UpperProfileCertificateData.prefix164 by rfl]
    exact UpperProfileCertificateData.row164_certificate
  · change RowCertified 165
    unfold RowCertified
    rw [show rowPrefix 165 = UpperProfileCertificateData.prefix165 by rfl]
    exact UpperProfileCertificateData.row165_certificate
  · change RowCertified 166
    unfold RowCertified
    rw [show rowPrefix 166 = UpperProfileCertificateData.prefix166 by rfl]
    exact UpperProfileCertificateData.row166_certificate
  · change RowCertified 167
    unfold RowCertified
    rw [show rowPrefix 167 = UpperProfileCertificateData.prefix167 by rfl]
    exact UpperProfileCertificateData.row167_certificate
  · change RowCertified 168
    unfold RowCertified
    rw [show rowPrefix 168 = UpperProfileCertificateData.prefix168 by rfl]
    exact UpperProfileCertificateData.row168_certificate
  · change RowCertified 169
    unfold RowCertified
    rw [show rowPrefix 169 = UpperProfileCertificateData.prefix169 by rfl]
    exact UpperProfileCertificateData.row169_certificate
  · change RowCertified 170
    unfold RowCertified
    rw [show rowPrefix 170 = UpperProfileCertificateData.prefix170 by rfl]
    exact UpperProfileCertificateData.row170_certificate
  · change RowCertified 171
    unfold RowCertified
    rw [show rowPrefix 171 = UpperProfileCertificateData.prefix171 by rfl]
    exact UpperProfileCertificateData.row171_certificate
  · change RowCertified 172
    unfold RowCertified
    rw [show rowPrefix 172 = UpperProfileCertificateData.prefix172 by rfl]
    exact UpperProfileCertificateData.row172_certificate
  · change RowCertified 173
    unfold RowCertified
    rw [show rowPrefix 173 = UpperProfileCertificateData.prefix173 by rfl]
    exact UpperProfileCertificateData.row173_certificate
  · change RowCertified 174
    unfold RowCertified
    rw [show rowPrefix 174 = UpperProfileCertificateData.prefix174 by rfl]
    exact UpperProfileCertificateData.row174_certificate
  · change RowCertified 175
    unfold RowCertified
    rw [show rowPrefix 175 = UpperProfileCertificateData.prefix175 by rfl]
    exact UpperProfileCertificateData.row175_certificate
  · change RowCertified 176
    unfold RowCertified
    rw [show rowPrefix 176 = UpperProfileCertificateData.prefix176 by rfl]
    exact UpperProfileCertificateData.row176_certificate
  · change RowCertified 177
    unfold RowCertified
    rw [show rowPrefix 177 = UpperProfileCertificateData.prefix177 by rfl]
    exact UpperProfileCertificateData.row177_certificate
  · change RowCertified 178
    unfold RowCertified
    rw [show rowPrefix 178 = UpperProfileCertificateData.prefix178 by rfl]
    exact UpperProfileCertificateData.row178_certificate
  · change RowCertified 179
    unfold RowCertified
    rw [show rowPrefix 179 = UpperProfileCertificateData.prefix179 by rfl]
    exact UpperProfileCertificateData.row179_certificate
  · change RowCertified 180
    unfold RowCertified
    rw [show rowPrefix 180 = UpperProfileCertificateData.prefix180 by rfl]
    exact UpperProfileCertificateData.row180_certificate
  · change RowCertified 181
    unfold RowCertified
    rw [show rowPrefix 181 = UpperProfileCertificateData.prefix181 by rfl]
    exact UpperProfileCertificateData.row181_certificate
  · change RowCertified 182
    unfold RowCertified
    rw [show rowPrefix 182 = UpperProfileCertificateData.prefix182 by rfl]
    exact UpperProfileCertificateData.row182_certificate
  · change RowCertified 183
    unfold RowCertified
    rw [show rowPrefix 183 = UpperProfileCertificateData.prefix183 by rfl]
    exact UpperProfileCertificateData.row183_certificate
  · change RowCertified 184
    unfold RowCertified
    rw [show rowPrefix 184 = UpperProfileCertificateData.prefix184 by rfl]
    exact UpperProfileCertificateData.row184_certificate
  · change RowCertified 185
    unfold RowCertified
    rw [show rowPrefix 185 = UpperProfileCertificateData.prefix185 by rfl]
    exact UpperProfileCertificateData.row185_certificate
  · change RowCertified 186
    unfold RowCertified
    rw [show rowPrefix 186 = UpperProfileCertificateData.prefix186 by rfl]
    exact UpperProfileCertificateData.row186_certificate
  · change RowCertified 187
    unfold RowCertified
    rw [show rowPrefix 187 = UpperProfileCertificateData.prefix187 by rfl]
    exact UpperProfileCertificateData.row187_certificate
  · change RowCertified 188
    unfold RowCertified
    rw [show rowPrefix 188 = UpperProfileCertificateData.prefix188 by rfl]
    exact UpperProfileCertificateData.row188_certificate
  · change RowCertified 189
    unfold RowCertified
    rw [show rowPrefix 189 = UpperProfileCertificateData.prefix189 by rfl]
    exact UpperProfileCertificateData.row189_certificate
  · change RowCertified 190
    unfold RowCertified
    rw [show rowPrefix 190 = UpperProfileCertificateData.prefix190 by rfl]
    exact UpperProfileCertificateData.row190_certificate
  · change RowCertified 191
    unfold RowCertified
    rw [show rowPrefix 191 = UpperProfileCertificateData.prefix191 by rfl]
    exact UpperProfileCertificateData.row191_certificate
  · change RowCertified 192
    unfold RowCertified
    rw [show rowPrefix 192 = UpperProfileCertificateData.prefix192 by rfl]
    exact UpperProfileCertificateData.row192_certificate
  · change RowCertified 193
    unfold RowCertified
    rw [show rowPrefix 193 = UpperProfileCertificateData.prefix193 by rfl]
    exact UpperProfileCertificateData.row193_certificate
  · change RowCertified 194
    unfold RowCertified
    rw [show rowPrefix 194 = UpperProfileCertificateData.prefix194 by rfl]
    exact UpperProfileCertificateData.row194_certificate
  · change RowCertified 195
    unfold RowCertified
    rw [show rowPrefix 195 = UpperProfileCertificateData.prefix195 by rfl]
    exact UpperProfileCertificateData.row195_certificate
  · change RowCertified 196
    unfold RowCertified
    rw [show rowPrefix 196 = UpperProfileCertificateData.prefix196 by rfl]
    exact UpperProfileCertificateData.row196_certificate
  · change RowCertified 197
    unfold RowCertified
    rw [show rowPrefix 197 = UpperProfileCertificateData.prefix197 by rfl]
    exact UpperProfileCertificateData.row197_certificate
  · change RowCertified 198
    unfold RowCertified
    rw [show rowPrefix 198 = UpperProfileCertificateData.prefix198 by rfl]
    exact UpperProfileCertificateData.row198_certificate
  · change RowCertified 199
    unfold RowCertified
    rw [show rowPrefix 199 = UpperProfileCertificateData.prefix199 by rfl]
    exact UpperProfileCertificateData.row199_certificate
  · change RowCertified 200
    unfold RowCertified
    rw [show rowPrefix 200 = UpperProfileCertificateData.prefix200 by rfl]
    exact UpperProfileCertificateData.row200_certificate
  · change RowCertified 201
    unfold RowCertified
    rw [show rowPrefix 201 = UpperProfileCertificateData.prefix201 by rfl]
    exact UpperProfileCertificateData.row201_certificate
  · change RowCertified 202
    unfold RowCertified
    rw [show rowPrefix 202 = UpperProfileCertificateData.prefix202 by rfl]
    exact UpperProfileCertificateData.row202_certificate
  · change RowCertified 203
    unfold RowCertified
    rw [show rowPrefix 203 = UpperProfileCertificateData.prefix203 by rfl]
    exact UpperProfileCertificateData.row203_certificate
  · change RowCertified 204
    unfold RowCertified
    rw [show rowPrefix 204 = UpperProfileCertificateData.prefix204 by rfl]
    exact UpperProfileCertificateData.row204_certificate
  · change RowCertified 205
    unfold RowCertified
    rw [show rowPrefix 205 = UpperProfileCertificateData.prefix205 by rfl]
    exact UpperProfileCertificateData.row205_certificate
  · change RowCertified 206
    unfold RowCertified
    rw [show rowPrefix 206 = UpperProfileCertificateData.prefix206 by rfl]
    exact UpperProfileCertificateData.row206_certificate
  · change RowCertified 207
    unfold RowCertified
    rw [show rowPrefix 207 = UpperProfileCertificateData.prefix207 by rfl]
    exact UpperProfileCertificateData.row207_certificate
  · change RowCertified 208
    unfold RowCertified
    rw [show rowPrefix 208 = UpperProfileCertificateData.prefix208 by rfl]
    exact UpperProfileCertificateData.row208_certificate
  · change RowCertified 209
    unfold RowCertified
    rw [show rowPrefix 209 = UpperProfileCertificateData.prefix209 by rfl]
    exact UpperProfileCertificateData.row209_certificate
  · change RowCertified 210
    unfold RowCertified
    rw [show rowPrefix 210 = UpperProfileCertificateData.prefix210 by rfl]
    exact UpperProfileCertificateData.row210_certificate
  · change RowCertified 211
    unfold RowCertified
    rw [show rowPrefix 211 = UpperProfileCertificateData.prefix211 by rfl]
    exact UpperProfileCertificateData.row211_certificate
  · change RowCertified 212
    unfold RowCertified
    rw [show rowPrefix 212 = UpperProfileCertificateData.prefix212 by rfl]
    exact UpperProfileCertificateData.row212_certificate
  · change RowCertified 213
    unfold RowCertified
    rw [show rowPrefix 213 = UpperProfileCertificateData.prefix213 by rfl]
    exact UpperProfileCertificateData.row213_certificate
  · change RowCertified 214
    unfold RowCertified
    rw [show rowPrefix 214 = UpperProfileCertificateData.prefix214 by rfl]
    exact UpperProfileCertificateData.row214_certificate
  · change RowCertified 215
    unfold RowCertified
    rw [show rowPrefix 215 = UpperProfileCertificateData.prefix215 by rfl]
    exact UpperProfileCertificateData.row215_certificate
  · change RowCertified 216
    unfold RowCertified
    rw [show rowPrefix 216 = UpperProfileCertificateData.prefix216 by rfl]
    exact UpperProfileCertificateData.row216_certificate
  · change RowCertified 217
    unfold RowCertified
    rw [show rowPrefix 217 = UpperProfileCertificateData.prefix217 by rfl]
    exact UpperProfileCertificateData.row217_certificate
  · change RowCertified 218
    unfold RowCertified
    rw [show rowPrefix 218 = UpperProfileCertificateData.prefix218 by rfl]
    exact UpperProfileCertificateData.row218_certificate
  · change RowCertified 219
    unfold RowCertified
    rw [show rowPrefix 219 = UpperProfileCertificateData.prefix219 by rfl]
    exact UpperProfileCertificateData.row219_certificate
  · change RowCertified 220
    unfold RowCertified
    rw [show rowPrefix 220 = UpperProfileCertificateData.prefix220 by rfl]
    exact UpperProfileCertificateData.row220_certificate
  · change RowCertified 221
    unfold RowCertified
    rw [show rowPrefix 221 = UpperProfileCertificateData.prefix221 by rfl]
    exact UpperProfileCertificateData.row221_certificate
  · change RowCertified 222
    unfold RowCertified
    rw [show rowPrefix 222 = UpperProfileCertificateData.prefix222 by rfl]
    exact UpperProfileCertificateData.row222_certificate
  · change RowCertified 223
    unfold RowCertified
    rw [show rowPrefix 223 = UpperProfileCertificateData.prefix223 by rfl]
    exact UpperProfileCertificateData.row223_certificate
  · change RowCertified 224
    unfold RowCertified
    rw [show rowPrefix 224 = UpperProfileCertificateData.prefix224 by rfl]
    exact UpperProfileCertificateData.row224_certificate
  · change RowCertified 225
    unfold RowCertified
    rw [show rowPrefix 225 = UpperProfileCertificateData.prefix225 by rfl]
    exact UpperProfileCertificateData.row225_certificate
  · change RowCertified 226
    unfold RowCertified
    rw [show rowPrefix 226 = UpperProfileCertificateData.prefix226 by rfl]
    exact UpperProfileCertificateData.row226_certificate
  · change RowCertified 227
    unfold RowCertified
    rw [show rowPrefix 227 = UpperProfileCertificateData.prefix227 by rfl]
    exact UpperProfileCertificateData.row227_certificate
  · change RowCertified 228
    unfold RowCertified
    rw [show rowPrefix 228 = UpperProfileCertificateData.prefix228 by rfl]
    exact UpperProfileCertificateData.row228_certificate
  · change RowCertified 229
    unfold RowCertified
    rw [show rowPrefix 229 = UpperProfileCertificateData.prefix229 by rfl]
    exact UpperProfileCertificateData.row229_certificate
  · change RowCertified 230
    unfold RowCertified
    rw [show rowPrefix 230 = UpperProfileCertificateData.prefix230 by rfl]
    exact UpperProfileCertificateData.row230_certificate
  · change RowCertified 231
    unfold RowCertified
    rw [show rowPrefix 231 = UpperProfileCertificateData.prefix231 by rfl]
    exact UpperProfileCertificateData.row231_certificate
  · change RowCertified 232
    unfold RowCertified
    rw [show rowPrefix 232 = UpperProfileCertificateData.prefix232 by rfl]
    exact UpperProfileCertificateData.row232_certificate
  · change RowCertified 233
    unfold RowCertified
    rw [show rowPrefix 233 = UpperProfileCertificateData.prefix233 by rfl]
    exact UpperProfileCertificateData.row233_certificate
  · change RowCertified 234
    unfold RowCertified
    rw [show rowPrefix 234 = UpperProfileCertificateData.prefix234 by rfl]
    exact UpperProfileCertificateData.row234_certificate
  · change RowCertified 235
    unfold RowCertified
    rw [show rowPrefix 235 = UpperProfileCertificateData.prefix235 by rfl]
    exact UpperProfileCertificateData.row235_certificate
  · change RowCertified 236
    unfold RowCertified
    rw [show rowPrefix 236 = UpperProfileCertificateData.prefix236 by rfl]
    exact UpperProfileCertificateData.row236_certificate
  · change RowCertified 237
    unfold RowCertified
    rw [show rowPrefix 237 = UpperProfileCertificateData.prefix237 by rfl]
    exact UpperProfileCertificateData.row237_certificate
  · change RowCertified 238
    unfold RowCertified
    rw [show rowPrefix 238 = UpperProfileCertificateData.prefix238 by rfl]
    exact UpperProfileCertificateData.row238_certificate
  · change RowCertified 239
    unfold RowCertified
    rw [show rowPrefix 239 = UpperProfileCertificateData.prefix239 by rfl]
    exact UpperProfileCertificateData.row239_certificate
run_cmd Lean.logInfo "FINER REAL INTERFACE: completed rows 120 through 239"
private theorem rows2 (i : Fin 120) : RowCertified (i.val+240) := by
  fin_cases i
  · change RowCertified 240
    unfold RowCertified
    rw [show rowPrefix 240 = UpperProfileCertificateData.prefix240 by rfl]
    exact UpperProfileCertificateData.row240_certificate
  · change RowCertified 241
    unfold RowCertified
    rw [show rowPrefix 241 = UpperProfileCertificateData.prefix241 by rfl]
    exact UpperProfileCertificateData.row241_certificate
  · change RowCertified 242
    unfold RowCertified
    rw [show rowPrefix 242 = UpperProfileCertificateData.prefix242 by rfl]
    exact UpperProfileCertificateData.row242_certificate
  · change RowCertified 243
    unfold RowCertified
    rw [show rowPrefix 243 = UpperProfileCertificateData.prefix243 by rfl]
    exact UpperProfileCertificateData.row243_certificate
  · change RowCertified 244
    unfold RowCertified
    rw [show rowPrefix 244 = UpperProfileCertificateData.prefix244 by rfl]
    exact UpperProfileCertificateData.row244_certificate
  · change RowCertified 245
    unfold RowCertified
    rw [show rowPrefix 245 = UpperProfileCertificateData.prefix245 by rfl]
    exact UpperProfileCertificateData.row245_certificate
  · change RowCertified 246
    unfold RowCertified
    rw [show rowPrefix 246 = UpperProfileCertificateData.prefix246 by rfl]
    exact UpperProfileCertificateData.row246_certificate
  · change RowCertified 247
    unfold RowCertified
    rw [show rowPrefix 247 = UpperProfileCertificateData.prefix247 by rfl]
    exact UpperProfileCertificateData.row247_certificate
  · change RowCertified 248
    unfold RowCertified
    rw [show rowPrefix 248 = UpperProfileCertificateData.prefix248 by rfl]
    exact UpperProfileCertificateData.row248_certificate
  · change RowCertified 249
    unfold RowCertified
    rw [show rowPrefix 249 = UpperProfileCertificateData.prefix249 by rfl]
    exact UpperProfileCertificateData.row249_certificate
  · change RowCertified 250
    unfold RowCertified
    rw [show rowPrefix 250 = UpperProfileCertificateData.prefix250 by rfl]
    exact UpperProfileCertificateData.row250_certificate
  · change RowCertified 251
    unfold RowCertified
    rw [show rowPrefix 251 = UpperProfileCertificateData.prefix251 by rfl]
    exact UpperProfileCertificateData.row251_certificate
  · change RowCertified 252
    unfold RowCertified
    rw [show rowPrefix 252 = UpperProfileCertificateData.prefix252 by rfl]
    exact UpperProfileCertificateData.row252_certificate
  · change RowCertified 253
    unfold RowCertified
    rw [show rowPrefix 253 = UpperProfileCertificateData.prefix253 by rfl]
    exact UpperProfileCertificateData.row253_certificate
  · change RowCertified 254
    unfold RowCertified
    rw [show rowPrefix 254 = UpperProfileCertificateData.prefix254 by rfl]
    exact UpperProfileCertificateData.row254_certificate
  · change RowCertified 255
    unfold RowCertified
    rw [show rowPrefix 255 = UpperProfileCertificateData.prefix255 by rfl]
    exact UpperProfileCertificateData.row255_certificate
  · change RowCertified 256
    unfold RowCertified
    rw [show rowPrefix 256 = UpperProfileCertificateData.prefix256 by rfl]
    exact UpperProfileCertificateData.row256_certificate
  · change RowCertified 257
    unfold RowCertified
    rw [show rowPrefix 257 = UpperProfileCertificateData.prefix257 by rfl]
    exact UpperProfileCertificateData.row257_certificate
  · change RowCertified 258
    unfold RowCertified
    rw [show rowPrefix 258 = UpperProfileCertificateData.prefix258 by rfl]
    exact UpperProfileCertificateData.row258_certificate
  · change RowCertified 259
    unfold RowCertified
    rw [show rowPrefix 259 = UpperProfileCertificateData.prefix259 by rfl]
    exact UpperProfileCertificateData.row259_certificate
  · change RowCertified 260
    unfold RowCertified
    rw [show rowPrefix 260 = UpperProfileCertificateData.prefix260 by rfl]
    exact UpperProfileCertificateData.row260_certificate
  · change RowCertified 261
    unfold RowCertified
    rw [show rowPrefix 261 = UpperProfileCertificateData.prefix261 by rfl]
    exact UpperProfileCertificateData.row261_certificate
  · change RowCertified 262
    unfold RowCertified
    rw [show rowPrefix 262 = UpperProfileCertificateData.prefix262 by rfl]
    exact UpperProfileCertificateData.row262_certificate
  · change RowCertified 263
    unfold RowCertified
    rw [show rowPrefix 263 = UpperProfileCertificateData.prefix263 by rfl]
    exact UpperProfileCertificateData.row263_certificate
  · change RowCertified 264
    unfold RowCertified
    rw [show rowPrefix 264 = UpperProfileCertificateData.prefix264 by rfl]
    exact UpperProfileCertificateData.row264_certificate
  · change RowCertified 265
    unfold RowCertified
    rw [show rowPrefix 265 = UpperProfileCertificateData.prefix265 by rfl]
    exact UpperProfileCertificateData.row265_certificate
  · change RowCertified 266
    unfold RowCertified
    rw [show rowPrefix 266 = UpperProfileCertificateData.prefix266 by rfl]
    exact UpperProfileCertificateData.row266_certificate
  · change RowCertified 267
    unfold RowCertified
    rw [show rowPrefix 267 = UpperProfileCertificateData.prefix267 by rfl]
    exact UpperProfileCertificateData.row267_certificate
  · change RowCertified 268
    unfold RowCertified
    rw [show rowPrefix 268 = UpperProfileCertificateData.prefix268 by rfl]
    exact UpperProfileCertificateData.row268_certificate
  · change RowCertified 269
    unfold RowCertified
    rw [show rowPrefix 269 = UpperProfileCertificateData.prefix269 by rfl]
    exact UpperProfileCertificateData.row269_certificate
  · change RowCertified 270
    unfold RowCertified
    rw [show rowPrefix 270 = UpperProfileCertificateData.prefix270 by rfl]
    exact UpperProfileCertificateData.row270_certificate
  · change RowCertified 271
    unfold RowCertified
    rw [show rowPrefix 271 = UpperProfileCertificateData.prefix271 by rfl]
    exact UpperProfileCertificateData.row271_certificate
  · change RowCertified 272
    unfold RowCertified
    rw [show rowPrefix 272 = UpperProfileCertificateData.prefix272 by rfl]
    exact UpperProfileCertificateData.row272_certificate
  · change RowCertified 273
    unfold RowCertified
    rw [show rowPrefix 273 = UpperProfileCertificateData.prefix273 by rfl]
    exact UpperProfileCertificateData.row273_certificate
  · change RowCertified 274
    unfold RowCertified
    rw [show rowPrefix 274 = UpperProfileCertificateData.prefix274 by rfl]
    exact UpperProfileCertificateData.row274_certificate
  · change RowCertified 275
    unfold RowCertified
    rw [show rowPrefix 275 = UpperProfileCertificateData.prefix275 by rfl]
    exact UpperProfileCertificateData.row275_certificate
  · change RowCertified 276
    unfold RowCertified
    rw [show rowPrefix 276 = UpperProfileCertificateData.prefix276 by rfl]
    exact UpperProfileCertificateData.row276_certificate
  · change RowCertified 277
    unfold RowCertified
    rw [show rowPrefix 277 = UpperProfileCertificateData.prefix277 by rfl]
    exact UpperProfileCertificateData.row277_certificate
  · change RowCertified 278
    unfold RowCertified
    rw [show rowPrefix 278 = UpperProfileCertificateData.prefix278 by rfl]
    exact UpperProfileCertificateData.row278_certificate
  · change RowCertified 279
    unfold RowCertified
    rw [show rowPrefix 279 = UpperProfileCertificateData.prefix279 by rfl]
    exact UpperProfileCertificateData.row279_certificate
  · change RowCertified 280
    unfold RowCertified
    rw [show rowPrefix 280 = UpperProfileCertificateData.prefix280 by rfl]
    exact UpperProfileCertificateData.row280_certificate
  · change RowCertified 281
    unfold RowCertified
    rw [show rowPrefix 281 = UpperProfileCertificateData.prefix281 by rfl]
    exact UpperProfileCertificateData.row281_certificate
  · change RowCertified 282
    unfold RowCertified
    rw [show rowPrefix 282 = UpperProfileCertificateData.prefix282 by rfl]
    exact UpperProfileCertificateData.row282_certificate
  · change RowCertified 283
    unfold RowCertified
    rw [show rowPrefix 283 = UpperProfileCertificateData.prefix283 by rfl]
    exact UpperProfileCertificateData.row283_certificate
  · change RowCertified 284
    unfold RowCertified
    rw [show rowPrefix 284 = UpperProfileCertificateData.prefix284 by rfl]
    exact UpperProfileCertificateData.row284_certificate
  · change RowCertified 285
    unfold RowCertified
    rw [show rowPrefix 285 = UpperProfileCertificateData.prefix285 by rfl]
    exact UpperProfileCertificateData.row285_certificate
  · change RowCertified 286
    unfold RowCertified
    rw [show rowPrefix 286 = UpperProfileCertificateData.prefix286 by rfl]
    exact UpperProfileCertificateData.row286_certificate
  · change RowCertified 287
    unfold RowCertified
    rw [show rowPrefix 287 = UpperProfileCertificateData.prefix287 by rfl]
    exact UpperProfileCertificateData.row287_certificate
  · change RowCertified 288
    unfold RowCertified
    rw [show rowPrefix 288 = UpperProfileCertificateData.prefix288 by rfl]
    exact UpperProfileCertificateData.row288_certificate
  · change RowCertified 289
    unfold RowCertified
    rw [show rowPrefix 289 = UpperProfileCertificateData.prefix289 by rfl]
    exact UpperProfileCertificateData.row289_certificate
  · change RowCertified 290
    unfold RowCertified
    rw [show rowPrefix 290 = UpperProfileCertificateData.prefix290 by rfl]
    exact UpperProfileCertificateData.row290_certificate
  · change RowCertified 291
    unfold RowCertified
    rw [show rowPrefix 291 = UpperProfileCertificateData.prefix291 by rfl]
    exact UpperProfileCertificateData.row291_certificate
  · change RowCertified 292
    unfold RowCertified
    rw [show rowPrefix 292 = UpperProfileCertificateData.prefix292 by rfl]
    exact UpperProfileCertificateData.row292_certificate
  · change RowCertified 293
    unfold RowCertified
    rw [show rowPrefix 293 = UpperProfileCertificateData.prefix293 by rfl]
    exact UpperProfileCertificateData.row293_certificate
  · change RowCertified 294
    unfold RowCertified
    rw [show rowPrefix 294 = UpperProfileCertificateData.prefix294 by rfl]
    exact UpperProfileCertificateData.row294_certificate
  · change RowCertified 295
    unfold RowCertified
    rw [show rowPrefix 295 = UpperProfileCertificateData.prefix295 by rfl]
    exact UpperProfileCertificateData.row295_certificate
  · change RowCertified 296
    unfold RowCertified
    rw [show rowPrefix 296 = UpperProfileCertificateData.prefix296 by rfl]
    exact UpperProfileCertificateData.row296_certificate
  · change RowCertified 297
    unfold RowCertified
    rw [show rowPrefix 297 = UpperProfileCertificateData.prefix297 by rfl]
    exact UpperProfileCertificateData.row297_certificate
  · change RowCertified 298
    unfold RowCertified
    rw [show rowPrefix 298 = UpperProfileCertificateData.prefix298 by rfl]
    exact UpperProfileCertificateData.row298_certificate
  · change RowCertified 299
    unfold RowCertified
    rw [show rowPrefix 299 = UpperProfileCertificateData.prefix299 by rfl]
    exact UpperProfileCertificateData.row299_certificate
  · change RowCertified 300
    unfold RowCertified
    rw [show rowPrefix 300 = UpperProfileCertificateData.prefix300 by rfl]
    exact UpperProfileCertificateData.row300_certificate
  · change RowCertified 301
    unfold RowCertified
    rw [show rowPrefix 301 = UpperProfileCertificateData.prefix301 by rfl]
    exact UpperProfileCertificateData.row301_certificate
  · change RowCertified 302
    unfold RowCertified
    rw [show rowPrefix 302 = UpperProfileCertificateData.prefix302 by rfl]
    exact UpperProfileCertificateData.row302_certificate
  · change RowCertified 303
    unfold RowCertified
    rw [show rowPrefix 303 = UpperProfileCertificateData.prefix303 by rfl]
    exact UpperProfileCertificateData.row303_certificate
  · change RowCertified 304
    unfold RowCertified
    rw [show rowPrefix 304 = UpperProfileCertificateData.prefix304 by rfl]
    exact UpperProfileCertificateData.row304_certificate
  · change RowCertified 305
    unfold RowCertified
    rw [show rowPrefix 305 = UpperProfileCertificateData.prefix305 by rfl]
    exact UpperProfileCertificateData.row305_certificate
  · change RowCertified 306
    unfold RowCertified
    rw [show rowPrefix 306 = UpperProfileCertificateData.prefix306 by rfl]
    exact UpperProfileCertificateData.row306_certificate
  · change RowCertified 307
    unfold RowCertified
    rw [show rowPrefix 307 = UpperProfileCertificateData.prefix307 by rfl]
    exact UpperProfileCertificateData.row307_certificate
  · change RowCertified 308
    unfold RowCertified
    rw [show rowPrefix 308 = UpperProfileCertificateData.prefix308 by rfl]
    exact UpperProfileCertificateData.row308_certificate
  · change RowCertified 309
    unfold RowCertified
    rw [show rowPrefix 309 = UpperProfileCertificateData.prefix309 by rfl]
    exact UpperProfileCertificateData.row309_certificate
  · change RowCertified 310
    unfold RowCertified
    rw [show rowPrefix 310 = UpperProfileCertificateData.prefix310 by rfl]
    exact UpperProfileCertificateData.row310_certificate
  · change RowCertified 311
    unfold RowCertified
    rw [show rowPrefix 311 = UpperProfileCertificateData.prefix311 by rfl]
    exact UpperProfileCertificateData.row311_certificate
  · change RowCertified 312
    unfold RowCertified
    rw [show rowPrefix 312 = UpperProfileCertificateData.prefix312 by rfl]
    exact UpperProfileCertificateData.row312_certificate
  · change RowCertified 313
    unfold RowCertified
    rw [show rowPrefix 313 = UpperProfileCertificateData.prefix313 by rfl]
    exact UpperProfileCertificateData.row313_certificate
  · change RowCertified 314
    unfold RowCertified
    rw [show rowPrefix 314 = UpperProfileCertificateData.prefix314 by rfl]
    exact UpperProfileCertificateData.row314_certificate
  · change RowCertified 315
    unfold RowCertified
    rw [show rowPrefix 315 = UpperProfileCertificateData.prefix315 by rfl]
    exact UpperProfileCertificateData.row315_certificate
  · change RowCertified 316
    unfold RowCertified
    rw [show rowPrefix 316 = UpperProfileCertificateData.prefix316 by rfl]
    exact UpperProfileCertificateData.row316_certificate
  · change RowCertified 317
    unfold RowCertified
    rw [show rowPrefix 317 = UpperProfileCertificateData.prefix317 by rfl]
    exact UpperProfileCertificateData.row317_certificate
  · change RowCertified 318
    unfold RowCertified
    rw [show rowPrefix 318 = UpperProfileCertificateData.prefix318 by rfl]
    exact UpperProfileCertificateData.row318_certificate
  · change RowCertified 319
    unfold RowCertified
    rw [show rowPrefix 319 = UpperProfileCertificateData.prefix319 by rfl]
    exact UpperProfileCertificateData.row319_certificate
  · change RowCertified 320
    unfold RowCertified
    rw [show rowPrefix 320 = UpperProfileCertificateData.prefix320 by rfl]
    exact UpperProfileCertificateData.row320_certificate
  · change RowCertified 321
    unfold RowCertified
    rw [show rowPrefix 321 = UpperProfileCertificateData.prefix321 by rfl]
    exact UpperProfileCertificateData.row321_certificate
  · change RowCertified 322
    unfold RowCertified
    rw [show rowPrefix 322 = UpperProfileCertificateData.prefix322 by rfl]
    exact UpperProfileCertificateData.row322_certificate
  · change RowCertified 323
    unfold RowCertified
    rw [show rowPrefix 323 = UpperProfileCertificateData.prefix323 by rfl]
    exact UpperProfileCertificateData.row323_certificate
  · change RowCertified 324
    unfold RowCertified
    rw [show rowPrefix 324 = UpperProfileCertificateData.prefix324 by rfl]
    exact UpperProfileCertificateData.row324_certificate
  · change RowCertified 325
    unfold RowCertified
    rw [show rowPrefix 325 = UpperProfileCertificateData.prefix325 by rfl]
    exact UpperProfileCertificateData.row325_certificate
  · change RowCertified 326
    unfold RowCertified
    rw [show rowPrefix 326 = UpperProfileCertificateData.prefix326 by rfl]
    exact UpperProfileCertificateData.row326_certificate
  · change RowCertified 327
    unfold RowCertified
    rw [show rowPrefix 327 = UpperProfileCertificateData.prefix327 by rfl]
    exact UpperProfileCertificateData.row327_certificate
  · change RowCertified 328
    unfold RowCertified
    rw [show rowPrefix 328 = UpperProfileCertificateData.prefix328 by rfl]
    exact UpperProfileCertificateData.row328_certificate
  · change RowCertified 329
    unfold RowCertified
    rw [show rowPrefix 329 = UpperProfileCertificateData.prefix329 by rfl]
    exact UpperProfileCertificateData.row329_certificate
  · change RowCertified 330
    unfold RowCertified
    rw [show rowPrefix 330 = UpperProfileCertificateData.prefix330 by rfl]
    exact UpperProfileCertificateData.row330_certificate
  · change RowCertified 331
    unfold RowCertified
    rw [show rowPrefix 331 = UpperProfileCertificateData.prefix331 by rfl]
    exact UpperProfileCertificateData.row331_certificate
  · change RowCertified 332
    unfold RowCertified
    rw [show rowPrefix 332 = UpperProfileCertificateData.prefix332 by rfl]
    exact UpperProfileCertificateData.row332_certificate
  · change RowCertified 333
    unfold RowCertified
    rw [show rowPrefix 333 = UpperProfileCertificateData.prefix333 by rfl]
    exact UpperProfileCertificateData.row333_certificate
  · change RowCertified 334
    unfold RowCertified
    rw [show rowPrefix 334 = UpperProfileCertificateData.prefix334 by rfl]
    exact UpperProfileCertificateData.row334_certificate
  · change RowCertified 335
    unfold RowCertified
    rw [show rowPrefix 335 = UpperProfileCertificateData.prefix335 by rfl]
    exact UpperProfileCertificateData.row335_certificate
  · change RowCertified 336
    unfold RowCertified
    rw [show rowPrefix 336 = UpperProfileCertificateData.prefix336 by rfl]
    exact UpperProfileCertificateData.row336_certificate
  · change RowCertified 337
    unfold RowCertified
    rw [show rowPrefix 337 = UpperProfileCertificateData.prefix337 by rfl]
    exact UpperProfileCertificateData.row337_certificate
  · change RowCertified 338
    unfold RowCertified
    rw [show rowPrefix 338 = UpperProfileCertificateData.prefix338 by rfl]
    exact UpperProfileCertificateData.row338_certificate
  · change RowCertified 339
    unfold RowCertified
    rw [show rowPrefix 339 = UpperProfileCertificateData.prefix339 by rfl]
    exact UpperProfileCertificateData.row339_certificate
  · change RowCertified 340
    unfold RowCertified
    rw [show rowPrefix 340 = UpperProfileCertificateData.prefix340 by rfl]
    exact UpperProfileCertificateData.row340_certificate
  · change RowCertified 341
    unfold RowCertified
    rw [show rowPrefix 341 = UpperProfileCertificateData.prefix341 by rfl]
    exact UpperProfileCertificateData.row341_certificate
  · change RowCertified 342
    unfold RowCertified
    rw [show rowPrefix 342 = UpperProfileCertificateData.prefix342 by rfl]
    exact UpperProfileCertificateData.row342_certificate
  · change RowCertified 343
    unfold RowCertified
    rw [show rowPrefix 343 = UpperProfileCertificateData.prefix343 by rfl]
    exact UpperProfileCertificateData.row343_certificate
  · change RowCertified 344
    unfold RowCertified
    rw [show rowPrefix 344 = UpperProfileCertificateData.prefix344 by rfl]
    exact UpperProfileCertificateData.row344_certificate
  · change RowCertified 345
    unfold RowCertified
    rw [show rowPrefix 345 = UpperProfileCertificateData.prefix345 by rfl]
    exact UpperProfileCertificateData.row345_certificate
  · change RowCertified 346
    unfold RowCertified
    rw [show rowPrefix 346 = UpperProfileCertificateData.prefix346 by rfl]
    exact UpperProfileCertificateData.row346_certificate
  · change RowCertified 347
    unfold RowCertified
    rw [show rowPrefix 347 = UpperProfileCertificateData.prefix347 by rfl]
    exact UpperProfileCertificateData.row347_certificate
  · change RowCertified 348
    unfold RowCertified
    rw [show rowPrefix 348 = UpperProfileCertificateData.prefix348 by rfl]
    exact UpperProfileCertificateData.row348_certificate
  · change RowCertified 349
    unfold RowCertified
    rw [show rowPrefix 349 = UpperProfileCertificateData.prefix349 by rfl]
    exact UpperProfileCertificateData.row349_certificate
  · change RowCertified 350
    unfold RowCertified
    rw [show rowPrefix 350 = UpperProfileCertificateData.prefix350 by rfl]
    exact UpperProfileCertificateData.row350_certificate
  · change RowCertified 351
    unfold RowCertified
    rw [show rowPrefix 351 = UpperProfileCertificateData.prefix351 by rfl]
    exact UpperProfileCertificateData.row351_certificate
  · change RowCertified 352
    unfold RowCertified
    rw [show rowPrefix 352 = UpperProfileCertificateData.prefix352 by rfl]
    exact UpperProfileCertificateData.row352_certificate
  · change RowCertified 353
    unfold RowCertified
    rw [show rowPrefix 353 = UpperProfileCertificateData.prefix353 by rfl]
    exact UpperProfileCertificateData.row353_certificate
  · change RowCertified 354
    unfold RowCertified
    rw [show rowPrefix 354 = UpperProfileCertificateData.prefix354 by rfl]
    exact UpperProfileCertificateData.row354_certificate
  · change RowCertified 355
    unfold RowCertified
    rw [show rowPrefix 355 = UpperProfileCertificateData.prefix355 by rfl]
    exact UpperProfileCertificateData.row355_certificate
  · change RowCertified 356
    unfold RowCertified
    rw [show rowPrefix 356 = UpperProfileCertificateData.prefix356 by rfl]
    exact UpperProfileCertificateData.row356_certificate
  · change RowCertified 357
    unfold RowCertified
    rw [show rowPrefix 357 = UpperProfileCertificateData.prefix357 by rfl]
    exact UpperProfileCertificateData.row357_certificate
  · change RowCertified 358
    unfold RowCertified
    rw [show rowPrefix 358 = UpperProfileCertificateData.prefix358 by rfl]
    exact UpperProfileCertificateData.row358_certificate
  · change RowCertified 359
    unfold RowCertified
    rw [show rowPrefix 359 = UpperProfileCertificateData.prefix359 by rfl]
    exact UpperProfileCertificateData.row359_certificate
run_cmd Lean.logInfo "FINER REAL INTERFACE: completed rows 240 through 359"
private theorem rows3 (i : Fin 120) : RowCertified (i.val+360) := by
  fin_cases i
  · change RowCertified 360
    unfold RowCertified
    rw [show rowPrefix 360 = UpperProfileCertificateData.prefix360 by rfl]
    exact UpperProfileCertificateData.row360_certificate
  · change RowCertified 361
    unfold RowCertified
    rw [show rowPrefix 361 = UpperProfileCertificateData.prefix361 by rfl]
    exact UpperProfileCertificateData.row361_certificate
  · change RowCertified 362
    unfold RowCertified
    rw [show rowPrefix 362 = UpperProfileCertificateData.prefix362 by rfl]
    exact UpperProfileCertificateData.row362_certificate
  · change RowCertified 363
    unfold RowCertified
    rw [show rowPrefix 363 = UpperProfileCertificateData.prefix363 by rfl]
    exact UpperProfileCertificateData.row363_certificate
  · change RowCertified 364
    unfold RowCertified
    rw [show rowPrefix 364 = UpperProfileCertificateData.prefix364 by rfl]
    exact UpperProfileCertificateData.row364_certificate
  · change RowCertified 365
    unfold RowCertified
    rw [show rowPrefix 365 = UpperProfileCertificateData.prefix365 by rfl]
    exact UpperProfileCertificateData.row365_certificate
  · change RowCertified 366
    unfold RowCertified
    rw [show rowPrefix 366 = UpperProfileCertificateData.prefix366 by rfl]
    exact UpperProfileCertificateData.row366_certificate
  · change RowCertified 367
    unfold RowCertified
    rw [show rowPrefix 367 = UpperProfileCertificateData.prefix367 by rfl]
    exact UpperProfileCertificateData.row367_certificate
  · change RowCertified 368
    unfold RowCertified
    rw [show rowPrefix 368 = UpperProfileCertificateData.prefix368 by rfl]
    exact UpperProfileCertificateData.row368_certificate
  · change RowCertified 369
    unfold RowCertified
    rw [show rowPrefix 369 = UpperProfileCertificateData.prefix369 by rfl]
    exact UpperProfileCertificateData.row369_certificate
  · change RowCertified 370
    unfold RowCertified
    rw [show rowPrefix 370 = UpperProfileCertificateData.prefix370 by rfl]
    exact UpperProfileCertificateData.row370_certificate
  · change RowCertified 371
    unfold RowCertified
    rw [show rowPrefix 371 = UpperProfileCertificateData.prefix371 by rfl]
    exact UpperProfileCertificateData.row371_certificate
  · change RowCertified 372
    unfold RowCertified
    rw [show rowPrefix 372 = UpperProfileCertificateData.prefix372 by rfl]
    exact UpperProfileCertificateData.row372_certificate
  · change RowCertified 373
    unfold RowCertified
    rw [show rowPrefix 373 = UpperProfileCertificateData.prefix373 by rfl]
    exact UpperProfileCertificateData.row373_certificate
  · change RowCertified 374
    unfold RowCertified
    rw [show rowPrefix 374 = UpperProfileCertificateData.prefix374 by rfl]
    exact UpperProfileCertificateData.row374_certificate
  · change RowCertified 375
    unfold RowCertified
    rw [show rowPrefix 375 = UpperProfileCertificateData.prefix375 by rfl]
    exact UpperProfileCertificateData.row375_certificate
  · change RowCertified 376
    unfold RowCertified
    rw [show rowPrefix 376 = UpperProfileCertificateData.prefix376 by rfl]
    exact UpperProfileCertificateData.row376_certificate
  · change RowCertified 377
    unfold RowCertified
    rw [show rowPrefix 377 = UpperProfileCertificateData.prefix377 by rfl]
    exact UpperProfileCertificateData.row377_certificate
  · change RowCertified 378
    unfold RowCertified
    rw [show rowPrefix 378 = UpperProfileCertificateData.prefix378 by rfl]
    exact UpperProfileCertificateData.row378_certificate
  · change RowCertified 379
    unfold RowCertified
    rw [show rowPrefix 379 = UpperProfileCertificateData.prefix379 by rfl]
    exact UpperProfileCertificateData.row379_certificate
  · change RowCertified 380
    unfold RowCertified
    rw [show rowPrefix 380 = UpperProfileCertificateData.prefix380 by rfl]
    exact UpperProfileCertificateData.row380_certificate
  · change RowCertified 381
    unfold RowCertified
    rw [show rowPrefix 381 = UpperProfileCertificateData.prefix381 by rfl]
    exact UpperProfileCertificateData.row381_certificate
  · change RowCertified 382
    unfold RowCertified
    rw [show rowPrefix 382 = UpperProfileCertificateData.prefix382 by rfl]
    exact UpperProfileCertificateData.row382_certificate
  · change RowCertified 383
    unfold RowCertified
    rw [show rowPrefix 383 = UpperProfileCertificateData.prefix383 by rfl]
    exact UpperProfileCertificateData.row383_certificate
  · change RowCertified 384
    unfold RowCertified
    rw [show rowPrefix 384 = UpperProfileCertificateData.prefix384 by rfl]
    exact UpperProfileCertificateData.row384_certificate
  · change RowCertified 385
    unfold RowCertified
    rw [show rowPrefix 385 = UpperProfileCertificateData.prefix385 by rfl]
    exact UpperProfileCertificateData.row385_certificate
  · change RowCertified 386
    unfold RowCertified
    rw [show rowPrefix 386 = UpperProfileCertificateData.prefix386 by rfl]
    exact UpperProfileCertificateData.row386_certificate
  · change RowCertified 387
    unfold RowCertified
    rw [show rowPrefix 387 = UpperProfileCertificateData.prefix387 by rfl]
    exact UpperProfileCertificateData.row387_certificate
  · change RowCertified 388
    unfold RowCertified
    rw [show rowPrefix 388 = UpperProfileCertificateData.prefix388 by rfl]
    exact UpperProfileCertificateData.row388_certificate
  · change RowCertified 389
    unfold RowCertified
    rw [show rowPrefix 389 = UpperProfileCertificateData.prefix389 by rfl]
    exact UpperProfileCertificateData.row389_certificate
  · change RowCertified 390
    unfold RowCertified
    rw [show rowPrefix 390 = UpperProfileCertificateData.prefix390 by rfl]
    exact UpperProfileCertificateData.row390_certificate
  · change RowCertified 391
    unfold RowCertified
    rw [show rowPrefix 391 = UpperProfileCertificateData.prefix391 by rfl]
    exact UpperProfileCertificateData.row391_certificate
  · change RowCertified 392
    unfold RowCertified
    rw [show rowPrefix 392 = UpperProfileCertificateData.prefix392 by rfl]
    exact UpperProfileCertificateData.row392_certificate
  · change RowCertified 393
    unfold RowCertified
    rw [show rowPrefix 393 = UpperProfileCertificateData.prefix393 by rfl]
    exact UpperProfileCertificateData.row393_certificate
  · change RowCertified 394
    unfold RowCertified
    rw [show rowPrefix 394 = UpperProfileCertificateData.prefix394 by rfl]
    exact UpperProfileCertificateData.row394_certificate
  · change RowCertified 395
    unfold RowCertified
    rw [show rowPrefix 395 = UpperProfileCertificateData.prefix395 by rfl]
    exact UpperProfileCertificateData.row395_certificate
  · change RowCertified 396
    unfold RowCertified
    rw [show rowPrefix 396 = UpperProfileCertificateData.prefix396 by rfl]
    exact UpperProfileCertificateData.row396_certificate
  · change RowCertified 397
    unfold RowCertified
    rw [show rowPrefix 397 = UpperProfileCertificateData.prefix397 by rfl]
    exact UpperProfileCertificateData.row397_certificate
  · change RowCertified 398
    unfold RowCertified
    rw [show rowPrefix 398 = UpperProfileCertificateData.prefix398 by rfl]
    exact UpperProfileCertificateData.row398_certificate
  · change RowCertified 399
    unfold RowCertified
    rw [show rowPrefix 399 = UpperProfileCertificateData.prefix399 by rfl]
    exact UpperProfileCertificateData.row399_certificate
  · change RowCertified 400
    unfold RowCertified
    rw [show rowPrefix 400 = UpperProfileCertificateData.prefix400 by rfl]
    exact UpperProfileCertificateData.row400_certificate
  · change RowCertified 401
    unfold RowCertified
    rw [show rowPrefix 401 = UpperProfileCertificateData.prefix401 by rfl]
    exact UpperProfileCertificateData.row401_certificate
  · change RowCertified 402
    unfold RowCertified
    rw [show rowPrefix 402 = UpperProfileCertificateData.prefix402 by rfl]
    exact UpperProfileCertificateData.row402_certificate
  · change RowCertified 403
    unfold RowCertified
    rw [show rowPrefix 403 = UpperProfileCertificateData.prefix403 by rfl]
    exact UpperProfileCertificateData.row403_certificate
  · change RowCertified 404
    unfold RowCertified
    rw [show rowPrefix 404 = UpperProfileCertificateData.prefix404 by rfl]
    exact UpperProfileCertificateData.row404_certificate
  · change RowCertified 405
    unfold RowCertified
    rw [show rowPrefix 405 = UpperProfileCertificateData.prefix405 by rfl]
    exact UpperProfileCertificateData.row405_certificate
  · change RowCertified 406
    unfold RowCertified
    rw [show rowPrefix 406 = UpperProfileCertificateData.prefix406 by rfl]
    exact UpperProfileCertificateData.row406_certificate
  · change RowCertified 407
    unfold RowCertified
    rw [show rowPrefix 407 = UpperProfileCertificateData.prefix407 by rfl]
    exact UpperProfileCertificateData.row407_certificate
  · change RowCertified 408
    unfold RowCertified
    rw [show rowPrefix 408 = UpperProfileCertificateData.prefix408 by rfl]
    exact UpperProfileCertificateData.row408_certificate
  · change RowCertified 409
    unfold RowCertified
    rw [show rowPrefix 409 = UpperProfileCertificateData.prefix409 by rfl]
    exact UpperProfileCertificateData.row409_certificate
  · change RowCertified 410
    unfold RowCertified
    rw [show rowPrefix 410 = UpperProfileCertificateData.prefix410 by rfl]
    exact UpperProfileCertificateData.row410_certificate
  · change RowCertified 411
    unfold RowCertified
    rw [show rowPrefix 411 = UpperProfileCertificateData.prefix411 by rfl]
    exact UpperProfileCertificateData.row411_certificate
  · change RowCertified 412
    unfold RowCertified
    rw [show rowPrefix 412 = UpperProfileCertificateData.prefix412 by rfl]
    exact UpperProfileCertificateData.row412_certificate
  · change RowCertified 413
    unfold RowCertified
    rw [show rowPrefix 413 = UpperProfileCertificateData.prefix413 by rfl]
    exact UpperProfileCertificateData.row413_certificate
  · change RowCertified 414
    unfold RowCertified
    rw [show rowPrefix 414 = UpperProfileCertificateData.prefix414 by rfl]
    exact UpperProfileCertificateData.row414_certificate
  · change RowCertified 415
    unfold RowCertified
    rw [show rowPrefix 415 = UpperProfileCertificateData.prefix415 by rfl]
    exact UpperProfileCertificateData.row415_certificate
  · change RowCertified 416
    unfold RowCertified
    rw [show rowPrefix 416 = UpperProfileCertificateData.prefix416 by rfl]
    exact UpperProfileCertificateData.row416_certificate
  · change RowCertified 417
    unfold RowCertified
    rw [show rowPrefix 417 = UpperProfileCertificateData.prefix417 by rfl]
    exact UpperProfileCertificateData.row417_certificate
  · change RowCertified 418
    unfold RowCertified
    rw [show rowPrefix 418 = UpperProfileCertificateData.prefix418 by rfl]
    exact UpperProfileCertificateData.row418_certificate
  · change RowCertified 419
    unfold RowCertified
    rw [show rowPrefix 419 = UpperProfileCertificateData.prefix419 by rfl]
    exact UpperProfileCertificateData.row419_certificate
  · change RowCertified 420
    unfold RowCertified
    rw [show rowPrefix 420 = UpperProfileCertificateData.prefix420 by rfl]
    exact UpperProfileCertificateData.row420_certificate
  · change RowCertified 421
    unfold RowCertified
    rw [show rowPrefix 421 = UpperProfileCertificateData.prefix421 by rfl]
    exact UpperProfileCertificateData.row421_certificate
  · change RowCertified 422
    unfold RowCertified
    rw [show rowPrefix 422 = UpperProfileCertificateData.prefix422 by rfl]
    exact UpperProfileCertificateData.row422_certificate
  · change RowCertified 423
    unfold RowCertified
    rw [show rowPrefix 423 = UpperProfileCertificateData.prefix423 by rfl]
    exact UpperProfileCertificateData.row423_certificate
  · change RowCertified 424
    unfold RowCertified
    rw [show rowPrefix 424 = UpperProfileCertificateData.prefix424 by rfl]
    exact UpperProfileCertificateData.row424_certificate
  · change RowCertified 425
    unfold RowCertified
    rw [show rowPrefix 425 = UpperProfileCertificateData.prefix425 by rfl]
    exact UpperProfileCertificateData.row425_certificate
  · change RowCertified 426
    unfold RowCertified
    rw [show rowPrefix 426 = UpperProfileCertificateData.prefix426 by rfl]
    exact UpperProfileCertificateData.row426_certificate
  · change RowCertified 427
    unfold RowCertified
    rw [show rowPrefix 427 = UpperProfileCertificateData.prefix427 by rfl]
    exact UpperProfileCertificateData.row427_certificate
  · change RowCertified 428
    unfold RowCertified
    rw [show rowPrefix 428 = UpperProfileCertificateData.prefix428 by rfl]
    exact UpperProfileCertificateData.row428_certificate
  · change RowCertified 429
    unfold RowCertified
    rw [show rowPrefix 429 = UpperProfileCertificateData.prefix429 by rfl]
    exact UpperProfileCertificateData.row429_certificate
  · change RowCertified 430
    unfold RowCertified
    rw [show rowPrefix 430 = UpperProfileCertificateData.prefix430 by rfl]
    exact UpperProfileCertificateData.row430_certificate
  · change RowCertified 431
    unfold RowCertified
    rw [show rowPrefix 431 = UpperProfileCertificateData.prefix431 by rfl]
    exact UpperProfileCertificateData.row431_certificate
  · change RowCertified 432
    unfold RowCertified
    rw [show rowPrefix 432 = UpperProfileCertificateData.prefix432 by rfl]
    exact UpperProfileCertificateData.row432_certificate
  · change RowCertified 433
    unfold RowCertified
    rw [show rowPrefix 433 = UpperProfileCertificateData.prefix433 by rfl]
    exact UpperProfileCertificateData.row433_certificate
  · change RowCertified 434
    unfold RowCertified
    rw [show rowPrefix 434 = UpperProfileCertificateData.prefix434 by rfl]
    exact UpperProfileCertificateData.row434_certificate
  · change RowCertified 435
    unfold RowCertified
    rw [show rowPrefix 435 = UpperProfileCertificateData.prefix435 by rfl]
    exact UpperProfileCertificateData.row435_certificate
  · change RowCertified 436
    unfold RowCertified
    rw [show rowPrefix 436 = UpperProfileCertificateData.prefix436 by rfl]
    exact UpperProfileCertificateData.row436_certificate
  · change RowCertified 437
    unfold RowCertified
    rw [show rowPrefix 437 = UpperProfileCertificateData.prefix437 by rfl]
    exact UpperProfileCertificateData.row437_certificate
  · change RowCertified 438
    unfold RowCertified
    rw [show rowPrefix 438 = UpperProfileCertificateData.prefix438 by rfl]
    exact UpperProfileCertificateData.row438_certificate
  · change RowCertified 439
    unfold RowCertified
    rw [show rowPrefix 439 = UpperProfileCertificateData.prefix439 by rfl]
    exact UpperProfileCertificateData.row439_certificate
  · change RowCertified 440
    unfold RowCertified
    rw [show rowPrefix 440 = UpperProfileCertificateData.prefix440 by rfl]
    exact UpperProfileCertificateData.row440_certificate
  · change RowCertified 441
    unfold RowCertified
    rw [show rowPrefix 441 = UpperProfileCertificateData.prefix441 by rfl]
    exact UpperProfileCertificateData.row441_certificate
  · change RowCertified 442
    unfold RowCertified
    rw [show rowPrefix 442 = UpperProfileCertificateData.prefix442 by rfl]
    exact UpperProfileCertificateData.row442_certificate
  · change RowCertified 443
    unfold RowCertified
    rw [show rowPrefix 443 = UpperProfileCertificateData.prefix443 by rfl]
    exact UpperProfileCertificateData.row443_certificate
  · change RowCertified 444
    unfold RowCertified
    rw [show rowPrefix 444 = UpperProfileCertificateData.prefix444 by rfl]
    exact UpperProfileCertificateData.row444_certificate
  · change RowCertified 445
    unfold RowCertified
    rw [show rowPrefix 445 = UpperProfileCertificateData.prefix445 by rfl]
    exact UpperProfileCertificateData.row445_certificate
  · change RowCertified 446
    unfold RowCertified
    rw [show rowPrefix 446 = UpperProfileCertificateData.prefix446 by rfl]
    exact UpperProfileCertificateData.row446_certificate
  · change RowCertified 447
    unfold RowCertified
    rw [show rowPrefix 447 = UpperProfileCertificateData.prefix447 by rfl]
    exact UpperProfileCertificateData.row447_certificate
  · change RowCertified 448
    unfold RowCertified
    rw [show rowPrefix 448 = UpperProfileCertificateData.prefix448 by rfl]
    exact UpperProfileCertificateData.row448_certificate
  · change RowCertified 449
    unfold RowCertified
    rw [show rowPrefix 449 = UpperProfileCertificateData.prefix449 by rfl]
    exact UpperProfileCertificateData.row449_certificate
  · change RowCertified 450
    unfold RowCertified
    rw [show rowPrefix 450 = UpperProfileCertificateData.prefix450 by rfl]
    exact UpperProfileCertificateData.row450_certificate
  · change RowCertified 451
    unfold RowCertified
    rw [show rowPrefix 451 = UpperProfileCertificateData.prefix451 by rfl]
    exact UpperProfileCertificateData.row451_certificate
  · change RowCertified 452
    unfold RowCertified
    rw [show rowPrefix 452 = UpperProfileCertificateData.prefix452 by rfl]
    exact UpperProfileCertificateData.row452_certificate
  · change RowCertified 453
    unfold RowCertified
    rw [show rowPrefix 453 = UpperProfileCertificateData.prefix453 by rfl]
    exact UpperProfileCertificateData.row453_certificate
  · change RowCertified 454
    unfold RowCertified
    rw [show rowPrefix 454 = UpperProfileCertificateData.prefix454 by rfl]
    exact UpperProfileCertificateData.row454_certificate
  · change RowCertified 455
    unfold RowCertified
    rw [show rowPrefix 455 = UpperProfileCertificateData.prefix455 by rfl]
    exact UpperProfileCertificateData.row455_certificate
  · change RowCertified 456
    unfold RowCertified
    rw [show rowPrefix 456 = UpperProfileCertificateData.prefix456 by rfl]
    exact UpperProfileCertificateData.row456_certificate
  · change RowCertified 457
    unfold RowCertified
    rw [show rowPrefix 457 = UpperProfileCertificateData.prefix457 by rfl]
    exact UpperProfileCertificateData.row457_certificate
  · change RowCertified 458
    unfold RowCertified
    rw [show rowPrefix 458 = UpperProfileCertificateData.prefix458 by rfl]
    exact UpperProfileCertificateData.row458_certificate
  · change RowCertified 459
    unfold RowCertified
    rw [show rowPrefix 459 = UpperProfileCertificateData.prefix459 by rfl]
    exact UpperProfileCertificateData.row459_certificate
  · change RowCertified 460
    unfold RowCertified
    rw [show rowPrefix 460 = UpperProfileCertificateData.prefix460 by rfl]
    exact UpperProfileCertificateData.row460_certificate
  · change RowCertified 461
    unfold RowCertified
    rw [show rowPrefix 461 = UpperProfileCertificateData.prefix461 by rfl]
    exact UpperProfileCertificateData.row461_certificate
  · change RowCertified 462
    unfold RowCertified
    rw [show rowPrefix 462 = UpperProfileCertificateData.prefix462 by rfl]
    exact UpperProfileCertificateData.row462_certificate
  · change RowCertified 463
    unfold RowCertified
    rw [show rowPrefix 463 = UpperProfileCertificateData.prefix463 by rfl]
    exact UpperProfileCertificateData.row463_certificate
  · change RowCertified 464
    unfold RowCertified
    rw [show rowPrefix 464 = UpperProfileCertificateData.prefix464 by rfl]
    exact UpperProfileCertificateData.row464_certificate
  · change RowCertified 465
    unfold RowCertified
    rw [show rowPrefix 465 = UpperProfileCertificateData.prefix465 by rfl]
    exact UpperProfileCertificateData.row465_certificate
  · change RowCertified 466
    unfold RowCertified
    rw [show rowPrefix 466 = UpperProfileCertificateData.prefix466 by rfl]
    exact UpperProfileCertificateData.row466_certificate
  · change RowCertified 467
    unfold RowCertified
    rw [show rowPrefix 467 = UpperProfileCertificateData.prefix467 by rfl]
    exact UpperProfileCertificateData.row467_certificate
  · change RowCertified 468
    unfold RowCertified
    rw [show rowPrefix 468 = UpperProfileCertificateData.prefix468 by rfl]
    exact UpperProfileCertificateData.row468_certificate
  · change RowCertified 469
    unfold RowCertified
    rw [show rowPrefix 469 = UpperProfileCertificateData.prefix469 by rfl]
    exact UpperProfileCertificateData.row469_certificate
  · change RowCertified 470
    unfold RowCertified
    rw [show rowPrefix 470 = UpperProfileCertificateData.prefix470 by rfl]
    exact UpperProfileCertificateData.row470_certificate
  · change RowCertified 471
    unfold RowCertified
    rw [show rowPrefix 471 = UpperProfileCertificateData.prefix471 by rfl]
    exact UpperProfileCertificateData.row471_certificate
  · change RowCertified 472
    unfold RowCertified
    rw [show rowPrefix 472 = UpperProfileCertificateData.prefix472 by rfl]
    exact UpperProfileCertificateData.row472_certificate
  · change RowCertified 473
    unfold RowCertified
    rw [show rowPrefix 473 = UpperProfileCertificateData.prefix473 by rfl]
    exact UpperProfileCertificateData.row473_certificate
  · change RowCertified 474
    unfold RowCertified
    rw [show rowPrefix 474 = UpperProfileCertificateData.prefix474 by rfl]
    exact UpperProfileCertificateData.row474_certificate
  · change RowCertified 475
    unfold RowCertified
    rw [show rowPrefix 475 = UpperProfileCertificateData.prefix475 by rfl]
    exact UpperProfileCertificateData.row475_certificate
  · change RowCertified 476
    unfold RowCertified
    rw [show rowPrefix 476 = UpperProfileCertificateData.prefix476 by rfl]
    exact UpperProfileCertificateData.row476_certificate
  · change RowCertified 477
    unfold RowCertified
    rw [show rowPrefix 477 = UpperProfileCertificateData.prefix477 by rfl]
    exact UpperProfileCertificateData.row477_certificate
  · change RowCertified 478
    unfold RowCertified
    rw [show rowPrefix 478 = UpperProfileCertificateData.prefix478 by rfl]
    exact UpperProfileCertificateData.row478_certificate
  · change RowCertified 479
    unfold RowCertified
    rw [show rowPrefix 479 = UpperProfileCertificateData.prefix479 by rfl]
    exact UpperProfileCertificateData.row479_certificate
run_cmd Lean.logInfo "FINER REAL INTERFACE: completed rows 360 through 479"
private theorem rows4 (i : Fin 120) : RowCertified (i.val+480) := by
  fin_cases i
  · change RowCertified 480
    unfold RowCertified
    rw [show rowPrefix 480 = UpperProfileCertificateData.prefix480 by rfl]
    exact UpperProfileCertificateData.row480_certificate
  · change RowCertified 481
    unfold RowCertified
    rw [show rowPrefix 481 = UpperProfileCertificateData.prefix481 by rfl]
    exact UpperProfileCertificateData.row481_certificate
  · change RowCertified 482
    unfold RowCertified
    rw [show rowPrefix 482 = UpperProfileCertificateData.prefix482 by rfl]
    exact UpperProfileCertificateData.row482_certificate
  · change RowCertified 483
    unfold RowCertified
    rw [show rowPrefix 483 = UpperProfileCertificateData.prefix483 by rfl]
    exact UpperProfileCertificateData.row483_certificate
  · change RowCertified 484
    unfold RowCertified
    rw [show rowPrefix 484 = UpperProfileCertificateData.prefix484 by rfl]
    exact UpperProfileCertificateData.row484_certificate
  · change RowCertified 485
    unfold RowCertified
    rw [show rowPrefix 485 = UpperProfileCertificateData.prefix485 by rfl]
    exact UpperProfileCertificateData.row485_certificate
  · change RowCertified 486
    unfold RowCertified
    rw [show rowPrefix 486 = UpperProfileCertificateData.prefix486 by rfl]
    exact UpperProfileCertificateData.row486_certificate
  · change RowCertified 487
    unfold RowCertified
    rw [show rowPrefix 487 = UpperProfileCertificateData.prefix487 by rfl]
    exact UpperProfileCertificateData.row487_certificate
  · change RowCertified 488
    unfold RowCertified
    rw [show rowPrefix 488 = UpperProfileCertificateData.prefix488 by rfl]
    exact UpperProfileCertificateData.row488_certificate
  · change RowCertified 489
    unfold RowCertified
    rw [show rowPrefix 489 = UpperProfileCertificateData.prefix489 by rfl]
    exact UpperProfileCertificateData.row489_certificate
  · change RowCertified 490
    unfold RowCertified
    rw [show rowPrefix 490 = UpperProfileCertificateData.prefix490 by rfl]
    exact UpperProfileCertificateData.row490_certificate
  · change RowCertified 491
    unfold RowCertified
    rw [show rowPrefix 491 = UpperProfileCertificateData.prefix491 by rfl]
    exact UpperProfileCertificateData.row491_certificate
  · change RowCertified 492
    unfold RowCertified
    rw [show rowPrefix 492 = UpperProfileCertificateData.prefix492 by rfl]
    exact UpperProfileCertificateData.row492_certificate
  · change RowCertified 493
    unfold RowCertified
    rw [show rowPrefix 493 = UpperProfileCertificateData.prefix493 by rfl]
    exact UpperProfileCertificateData.row493_certificate
  · change RowCertified 494
    unfold RowCertified
    rw [show rowPrefix 494 = UpperProfileCertificateData.prefix494 by rfl]
    exact UpperProfileCertificateData.row494_certificate
  · change RowCertified 495
    unfold RowCertified
    rw [show rowPrefix 495 = UpperProfileCertificateData.prefix495 by rfl]
    exact UpperProfileCertificateData.row495_certificate
  · change RowCertified 496
    unfold RowCertified
    rw [show rowPrefix 496 = UpperProfileCertificateData.prefix496 by rfl]
    exact UpperProfileCertificateData.row496_certificate
  · change RowCertified 497
    unfold RowCertified
    rw [show rowPrefix 497 = UpperProfileCertificateData.prefix497 by rfl]
    exact UpperProfileCertificateData.row497_certificate
  · change RowCertified 498
    unfold RowCertified
    rw [show rowPrefix 498 = UpperProfileCertificateData.prefix498 by rfl]
    exact UpperProfileCertificateData.row498_certificate
  · change RowCertified 499
    unfold RowCertified
    rw [show rowPrefix 499 = UpperProfileCertificateData.prefix499 by rfl]
    exact UpperProfileCertificateData.row499_certificate
  · change RowCertified 500
    unfold RowCertified
    rw [show rowPrefix 500 = UpperProfileCertificateData.prefix500 by rfl]
    exact UpperProfileCertificateData.row500_certificate
  · change RowCertified 501
    unfold RowCertified
    rw [show rowPrefix 501 = UpperProfileCertificateData.prefix501 by rfl]
    exact UpperProfileCertificateData.row501_certificate
  · change RowCertified 502
    unfold RowCertified
    rw [show rowPrefix 502 = UpperProfileCertificateData.prefix502 by rfl]
    exact UpperProfileCertificateData.row502_certificate
  · change RowCertified 503
    unfold RowCertified
    rw [show rowPrefix 503 = UpperProfileCertificateData.prefix503 by rfl]
    exact UpperProfileCertificateData.row503_certificate
  · change RowCertified 504
    unfold RowCertified
    rw [show rowPrefix 504 = UpperProfileCertificateData.prefix504 by rfl]
    exact UpperProfileCertificateData.row504_certificate
  · change RowCertified 505
    unfold RowCertified
    rw [show rowPrefix 505 = UpperProfileCertificateData.prefix505 by rfl]
    exact UpperProfileCertificateData.row505_certificate
  · change RowCertified 506
    unfold RowCertified
    rw [show rowPrefix 506 = UpperProfileCertificateData.prefix506 by rfl]
    exact UpperProfileCertificateData.row506_certificate
  · change RowCertified 507
    unfold RowCertified
    rw [show rowPrefix 507 = UpperProfileCertificateData.prefix507 by rfl]
    exact UpperProfileCertificateData.row507_certificate
  · change RowCertified 508
    unfold RowCertified
    rw [show rowPrefix 508 = UpperProfileCertificateData.prefix508 by rfl]
    exact UpperProfileCertificateData.row508_certificate
  · change RowCertified 509
    unfold RowCertified
    rw [show rowPrefix 509 = UpperProfileCertificateData.prefix509 by rfl]
    exact UpperProfileCertificateData.row509_certificate
  · change RowCertified 510
    unfold RowCertified
    rw [show rowPrefix 510 = UpperProfileCertificateData.prefix510 by rfl]
    exact UpperProfileCertificateData.row510_certificate
  · change RowCertified 511
    unfold RowCertified
    rw [show rowPrefix 511 = UpperProfileCertificateData.prefix511 by rfl]
    exact UpperProfileCertificateData.row511_certificate
  · change RowCertified 512
    unfold RowCertified
    rw [show rowPrefix 512 = UpperProfileCertificateData.prefix512 by rfl]
    exact UpperProfileCertificateData.row512_certificate
  · change RowCertified 513
    unfold RowCertified
    rw [show rowPrefix 513 = UpperProfileCertificateData.prefix513 by rfl]
    exact UpperProfileCertificateData.row513_certificate
  · change RowCertified 514
    unfold RowCertified
    rw [show rowPrefix 514 = UpperProfileCertificateData.prefix514 by rfl]
    exact UpperProfileCertificateData.row514_certificate
  · change RowCertified 515
    unfold RowCertified
    rw [show rowPrefix 515 = UpperProfileCertificateData.prefix515 by rfl]
    exact UpperProfileCertificateData.row515_certificate
  · change RowCertified 516
    unfold RowCertified
    rw [show rowPrefix 516 = UpperProfileCertificateData.prefix516 by rfl]
    exact UpperProfileCertificateData.row516_certificate
  · change RowCertified 517
    unfold RowCertified
    rw [show rowPrefix 517 = UpperProfileCertificateData.prefix517 by rfl]
    exact UpperProfileCertificateData.row517_certificate
  · change RowCertified 518
    unfold RowCertified
    rw [show rowPrefix 518 = UpperProfileCertificateData.prefix518 by rfl]
    exact UpperProfileCertificateData.row518_certificate
  · change RowCertified 519
    unfold RowCertified
    rw [show rowPrefix 519 = UpperProfileCertificateData.prefix519 by rfl]
    exact UpperProfileCertificateData.row519_certificate
  · change RowCertified 520
    unfold RowCertified
    rw [show rowPrefix 520 = UpperProfileCertificateData.prefix520 by rfl]
    exact UpperProfileCertificateData.row520_certificate
  · change RowCertified 521
    unfold RowCertified
    rw [show rowPrefix 521 = UpperProfileCertificateData.prefix521 by rfl]
    exact UpperProfileCertificateData.row521_certificate
  · change RowCertified 522
    unfold RowCertified
    rw [show rowPrefix 522 = UpperProfileCertificateData.prefix522 by rfl]
    exact UpperProfileCertificateData.row522_certificate
  · change RowCertified 523
    unfold RowCertified
    rw [show rowPrefix 523 = UpperProfileCertificateData.prefix523 by rfl]
    exact UpperProfileCertificateData.row523_certificate
  · change RowCertified 524
    unfold RowCertified
    rw [show rowPrefix 524 = UpperProfileCertificateData.prefix524 by rfl]
    exact UpperProfileCertificateData.row524_certificate
  · change RowCertified 525
    unfold RowCertified
    rw [show rowPrefix 525 = UpperProfileCertificateData.prefix525 by rfl]
    exact UpperProfileCertificateData.row525_certificate
  · change RowCertified 526
    unfold RowCertified
    rw [show rowPrefix 526 = UpperProfileCertificateData.prefix526 by rfl]
    exact UpperProfileCertificateData.row526_certificate
  · change RowCertified 527
    unfold RowCertified
    rw [show rowPrefix 527 = UpperProfileCertificateData.prefix527 by rfl]
    exact UpperProfileCertificateData.row527_certificate
  · change RowCertified 528
    unfold RowCertified
    rw [show rowPrefix 528 = UpperProfileCertificateData.prefix528 by rfl]
    exact UpperProfileCertificateData.row528_certificate
  · change RowCertified 529
    unfold RowCertified
    rw [show rowPrefix 529 = UpperProfileCertificateData.prefix529 by rfl]
    exact UpperProfileCertificateData.row529_certificate
  · change RowCertified 530
    unfold RowCertified
    rw [show rowPrefix 530 = UpperProfileCertificateData.prefix530 by rfl]
    exact UpperProfileCertificateData.row530_certificate
  · change RowCertified 531
    unfold RowCertified
    rw [show rowPrefix 531 = UpperProfileCertificateData.prefix531 by rfl]
    exact UpperProfileCertificateData.row531_certificate
  · change RowCertified 532
    unfold RowCertified
    rw [show rowPrefix 532 = UpperProfileCertificateData.prefix532 by rfl]
    exact UpperProfileCertificateData.row532_certificate
  · change RowCertified 533
    unfold RowCertified
    rw [show rowPrefix 533 = UpperProfileCertificateData.prefix533 by rfl]
    exact UpperProfileCertificateData.row533_certificate
  · change RowCertified 534
    unfold RowCertified
    rw [show rowPrefix 534 = UpperProfileCertificateData.prefix534 by rfl]
    exact UpperProfileCertificateData.row534_certificate
  · change RowCertified 535
    unfold RowCertified
    rw [show rowPrefix 535 = UpperProfileCertificateData.prefix535 by rfl]
    exact UpperProfileCertificateData.row535_certificate
  · change RowCertified 536
    unfold RowCertified
    rw [show rowPrefix 536 = UpperProfileCertificateData.prefix536 by rfl]
    exact UpperProfileCertificateData.row536_certificate
  · change RowCertified 537
    unfold RowCertified
    rw [show rowPrefix 537 = UpperProfileCertificateData.prefix537 by rfl]
    exact UpperProfileCertificateData.row537_certificate
  · change RowCertified 538
    unfold RowCertified
    rw [show rowPrefix 538 = UpperProfileCertificateData.prefix538 by rfl]
    exact UpperProfileCertificateData.row538_certificate
  · change RowCertified 539
    unfold RowCertified
    rw [show rowPrefix 539 = UpperProfileCertificateData.prefix539 by rfl]
    exact UpperProfileCertificateData.row539_certificate
  · change RowCertified 540
    unfold RowCertified
    rw [show rowPrefix 540 = UpperProfileCertificateData.prefix540 by rfl]
    exact UpperProfileCertificateData.row540_certificate
  · change RowCertified 541
    unfold RowCertified
    rw [show rowPrefix 541 = UpperProfileCertificateData.prefix541 by rfl]
    exact UpperProfileCertificateData.row541_certificate
  · change RowCertified 542
    unfold RowCertified
    rw [show rowPrefix 542 = UpperProfileCertificateData.prefix542 by rfl]
    exact UpperProfileCertificateData.row542_certificate
  · change RowCertified 543
    unfold RowCertified
    rw [show rowPrefix 543 = UpperProfileCertificateData.prefix543 by rfl]
    exact UpperProfileCertificateData.row543_certificate
  · change RowCertified 544
    unfold RowCertified
    rw [show rowPrefix 544 = UpperProfileCertificateData.prefix544 by rfl]
    exact UpperProfileCertificateData.row544_certificate
  · change RowCertified 545
    unfold RowCertified
    rw [show rowPrefix 545 = UpperProfileCertificateData.prefix545 by rfl]
    exact UpperProfileCertificateData.row545_certificate
  · change RowCertified 546
    unfold RowCertified
    rw [show rowPrefix 546 = UpperProfileCertificateData.prefix546 by rfl]
    exact UpperProfileCertificateData.row546_certificate
  · change RowCertified 547
    unfold RowCertified
    rw [show rowPrefix 547 = UpperProfileCertificateData.prefix547 by rfl]
    exact UpperProfileCertificateData.row547_certificate
  · change RowCertified 548
    unfold RowCertified
    rw [show rowPrefix 548 = UpperProfileCertificateData.prefix548 by rfl]
    exact UpperProfileCertificateData.row548_certificate
  · change RowCertified 549
    unfold RowCertified
    rw [show rowPrefix 549 = UpperProfileCertificateData.prefix549 by rfl]
    exact UpperProfileCertificateData.row549_certificate
  · change RowCertified 550
    unfold RowCertified
    rw [show rowPrefix 550 = UpperProfileCertificateData.prefix550 by rfl]
    exact UpperProfileCertificateData.row550_certificate
  · change RowCertified 551
    unfold RowCertified
    rw [show rowPrefix 551 = UpperProfileCertificateData.prefix551 by rfl]
    exact UpperProfileCertificateData.row551_certificate
  · change RowCertified 552
    unfold RowCertified
    rw [show rowPrefix 552 = UpperProfileCertificateData.prefix552 by rfl]
    exact UpperProfileCertificateData.row552_certificate
  · change RowCertified 553
    unfold RowCertified
    rw [show rowPrefix 553 = UpperProfileCertificateData.prefix553 by rfl]
    exact UpperProfileCertificateData.row553_certificate
  · change RowCertified 554
    unfold RowCertified
    rw [show rowPrefix 554 = UpperProfileCertificateData.prefix554 by rfl]
    exact UpperProfileCertificateData.row554_certificate
  · change RowCertified 555
    unfold RowCertified
    rw [show rowPrefix 555 = UpperProfileCertificateData.prefix555 by rfl]
    exact UpperProfileCertificateData.row555_certificate
  · change RowCertified 556
    unfold RowCertified
    rw [show rowPrefix 556 = UpperProfileCertificateData.prefix556 by rfl]
    exact UpperProfileCertificateData.row556_certificate
  · change RowCertified 557
    unfold RowCertified
    rw [show rowPrefix 557 = UpperProfileCertificateData.prefix557 by rfl]
    exact UpperProfileCertificateData.row557_certificate
  · change RowCertified 558
    unfold RowCertified
    rw [show rowPrefix 558 = UpperProfileCertificateData.prefix558 by rfl]
    exact UpperProfileCertificateData.row558_certificate
  · change RowCertified 559
    unfold RowCertified
    rw [show rowPrefix 559 = UpperProfileCertificateData.prefix559 by rfl]
    exact UpperProfileCertificateData.row559_certificate
  · change RowCertified 560
    unfold RowCertified
    rw [show rowPrefix 560 = UpperProfileCertificateData.prefix560 by rfl]
    exact UpperProfileCertificateData.row560_certificate
  · change RowCertified 561
    unfold RowCertified
    rw [show rowPrefix 561 = UpperProfileCertificateData.prefix561 by rfl]
    exact UpperProfileCertificateData.row561_certificate
  · change RowCertified 562
    unfold RowCertified
    rw [show rowPrefix 562 = UpperProfileCertificateData.prefix562 by rfl]
    exact UpperProfileCertificateData.row562_certificate
  · change RowCertified 563
    unfold RowCertified
    rw [show rowPrefix 563 = UpperProfileCertificateData.prefix563 by rfl]
    exact UpperProfileCertificateData.row563_certificate
  · change RowCertified 564
    unfold RowCertified
    rw [show rowPrefix 564 = UpperProfileCertificateData.prefix564 by rfl]
    exact UpperProfileCertificateData.row564_certificate
  · change RowCertified 565
    unfold RowCertified
    rw [show rowPrefix 565 = UpperProfileCertificateData.prefix565 by rfl]
    exact UpperProfileCertificateData.row565_certificate
  · change RowCertified 566
    unfold RowCertified
    rw [show rowPrefix 566 = UpperProfileCertificateData.prefix566 by rfl]
    exact UpperProfileCertificateData.row566_certificate
  · change RowCertified 567
    unfold RowCertified
    rw [show rowPrefix 567 = UpperProfileCertificateData.prefix567 by rfl]
    exact UpperProfileCertificateData.row567_certificate
  · change RowCertified 568
    unfold RowCertified
    rw [show rowPrefix 568 = UpperProfileCertificateData.prefix568 by rfl]
    exact UpperProfileCertificateData.row568_certificate
  · change RowCertified 569
    unfold RowCertified
    rw [show rowPrefix 569 = UpperProfileCertificateData.prefix569 by rfl]
    exact UpperProfileCertificateData.row569_certificate
  · change RowCertified 570
    unfold RowCertified
    rw [show rowPrefix 570 = UpperProfileCertificateData.prefix570 by rfl]
    exact UpperProfileCertificateData.row570_certificate
  · change RowCertified 571
    unfold RowCertified
    rw [show rowPrefix 571 = UpperProfileCertificateData.prefix571 by rfl]
    exact UpperProfileCertificateData.row571_certificate
  · change RowCertified 572
    unfold RowCertified
    rw [show rowPrefix 572 = UpperProfileCertificateData.prefix572 by rfl]
    exact UpperProfileCertificateData.row572_certificate
  · change RowCertified 573
    unfold RowCertified
    rw [show rowPrefix 573 = UpperProfileCertificateData.prefix573 by rfl]
    exact UpperProfileCertificateData.row573_certificate
  · change RowCertified 574
    unfold RowCertified
    rw [show rowPrefix 574 = UpperProfileCertificateData.prefix574 by rfl]
    exact UpperProfileCertificateData.row574_certificate
  · change RowCertified 575
    unfold RowCertified
    rw [show rowPrefix 575 = UpperProfileCertificateData.prefix575 by rfl]
    exact UpperProfileCertificateData.row575_certificate
  · change RowCertified 576
    unfold RowCertified
    rw [show rowPrefix 576 = UpperProfileCertificateData.prefix576 by rfl]
    exact UpperProfileCertificateData.row576_certificate
  · change RowCertified 577
    unfold RowCertified
    rw [show rowPrefix 577 = UpperProfileCertificateData.prefix577 by rfl]
    exact UpperProfileCertificateData.row577_certificate
  · change RowCertified 578
    unfold RowCertified
    rw [show rowPrefix 578 = UpperProfileCertificateData.prefix578 by rfl]
    exact UpperProfileCertificateData.row578_certificate
  · change RowCertified 579
    unfold RowCertified
    rw [show rowPrefix 579 = UpperProfileCertificateData.prefix579 by rfl]
    exact UpperProfileCertificateData.row579_certificate
  · change RowCertified 580
    unfold RowCertified
    rw [show rowPrefix 580 = UpperProfileCertificateData.prefix580 by rfl]
    exact UpperProfileCertificateData.row580_certificate
  · change RowCertified 581
    unfold RowCertified
    rw [show rowPrefix 581 = UpperProfileCertificateData.prefix581 by rfl]
    exact UpperProfileCertificateData.row581_certificate
  · change RowCertified 582
    unfold RowCertified
    rw [show rowPrefix 582 = UpperProfileCertificateData.prefix582 by rfl]
    exact UpperProfileCertificateData.row582_certificate
  · change RowCertified 583
    unfold RowCertified
    rw [show rowPrefix 583 = UpperProfileCertificateData.prefix583 by rfl]
    exact UpperProfileCertificateData.row583_certificate
  · change RowCertified 584
    unfold RowCertified
    rw [show rowPrefix 584 = UpperProfileCertificateData.prefix584 by rfl]
    exact UpperProfileCertificateData.row584_certificate
  · change RowCertified 585
    unfold RowCertified
    rw [show rowPrefix 585 = UpperProfileCertificateData.prefix585 by rfl]
    exact UpperProfileCertificateData.row585_certificate
  · change RowCertified 586
    unfold RowCertified
    rw [show rowPrefix 586 = UpperProfileCertificateData.prefix586 by rfl]
    exact UpperProfileCertificateData.row586_certificate
  · change RowCertified 587
    unfold RowCertified
    rw [show rowPrefix 587 = UpperProfileCertificateData.prefix587 by rfl]
    exact UpperProfileCertificateData.row587_certificate
  · change RowCertified 588
    unfold RowCertified
    rw [show rowPrefix 588 = UpperProfileCertificateData.prefix588 by rfl]
    exact UpperProfileCertificateData.row588_certificate
  · change RowCertified 589
    unfold RowCertified
    rw [show rowPrefix 589 = UpperProfileCertificateData.prefix589 by rfl]
    exact UpperProfileCertificateData.row589_certificate
  · change RowCertified 590
    unfold RowCertified
    rw [show rowPrefix 590 = UpperProfileCertificateData.prefix590 by rfl]
    exact UpperProfileCertificateData.row590_certificate
  · change RowCertified 591
    unfold RowCertified
    rw [show rowPrefix 591 = UpperProfileCertificateData.prefix591 by rfl]
    exact UpperProfileCertificateData.row591_certificate
  · change RowCertified 592
    unfold RowCertified
    rw [show rowPrefix 592 = UpperProfileCertificateData.prefix592 by rfl]
    exact UpperProfileCertificateData.row592_certificate
  · change RowCertified 593
    unfold RowCertified
    rw [show rowPrefix 593 = UpperProfileCertificateData.prefix593 by rfl]
    exact UpperProfileCertificateData.row593_certificate
  · change RowCertified 594
    unfold RowCertified
    rw [show rowPrefix 594 = UpperProfileCertificateData.prefix594 by rfl]
    exact UpperProfileCertificateData.row594_certificate
  · change RowCertified 595
    unfold RowCertified
    rw [show rowPrefix 595 = UpperProfileCertificateData.prefix595 by rfl]
    exact UpperProfileCertificateData.row595_certificate
  · change RowCertified 596
    unfold RowCertified
    rw [show rowPrefix 596 = UpperProfileCertificateData.prefix596 by rfl]
    exact UpperProfileCertificateData.row596_certificate
  · change RowCertified 597
    unfold RowCertified
    rw [show rowPrefix 597 = UpperProfileCertificateData.prefix597 by rfl]
    exact UpperProfileCertificateData.row597_certificate
  · change RowCertified 598
    unfold RowCertified
    rw [show rowPrefix 598 = UpperProfileCertificateData.prefix598 by rfl]
    exact UpperProfileCertificateData.row598_certificate
  · change RowCertified 599
    unfold RowCertified
    rw [show rowPrefix 599 = UpperProfileCertificateData.prefix599 by rfl]
    exact UpperProfileCertificateData.row599_certificate
run_cmd Lean.logInfo "FINER REAL INTERFACE: completed rows 480 through 599"
private theorem rows5 (i : Fin 120) : RowCertified (i.val+600) := by
  fin_cases i
  · change RowCertified 600
    unfold RowCertified
    rw [show rowPrefix 600 = UpperProfileCertificateData.prefix600 by rfl]
    exact UpperProfileCertificateData.row600_certificate
  · change RowCertified 601
    unfold RowCertified
    rw [show rowPrefix 601 = UpperProfileCertificateData.prefix601 by rfl]
    exact UpperProfileCertificateData.row601_certificate
  · change RowCertified 602
    unfold RowCertified
    rw [show rowPrefix 602 = UpperProfileCertificateData.prefix602 by rfl]
    exact UpperProfileCertificateData.row602_certificate
  · change RowCertified 603
    unfold RowCertified
    rw [show rowPrefix 603 = UpperProfileCertificateData.prefix603 by rfl]
    exact UpperProfileCertificateData.row603_certificate
  · change RowCertified 604
    unfold RowCertified
    rw [show rowPrefix 604 = UpperProfileCertificateData.prefix604 by rfl]
    exact UpperProfileCertificateData.row604_certificate
  · change RowCertified 605
    unfold RowCertified
    rw [show rowPrefix 605 = UpperProfileCertificateData.prefix605 by rfl]
    exact UpperProfileCertificateData.row605_certificate
  · change RowCertified 606
    unfold RowCertified
    rw [show rowPrefix 606 = UpperProfileCertificateData.prefix606 by rfl]
    exact UpperProfileCertificateData.row606_certificate
  · change RowCertified 607
    unfold RowCertified
    rw [show rowPrefix 607 = UpperProfileCertificateData.prefix607 by rfl]
    exact UpperProfileCertificateData.row607_certificate
  · change RowCertified 608
    unfold RowCertified
    rw [show rowPrefix 608 = UpperProfileCertificateData.prefix608 by rfl]
    exact UpperProfileCertificateData.row608_certificate
  · change RowCertified 609
    unfold RowCertified
    rw [show rowPrefix 609 = UpperProfileCertificateData.prefix609 by rfl]
    exact UpperProfileCertificateData.row609_certificate
  · change RowCertified 610
    unfold RowCertified
    rw [show rowPrefix 610 = UpperProfileCertificateData.prefix610 by rfl]
    exact UpperProfileCertificateData.row610_certificate
  · change RowCertified 611
    unfold RowCertified
    rw [show rowPrefix 611 = UpperProfileCertificateData.prefix611 by rfl]
    exact UpperProfileCertificateData.row611_certificate
  · change RowCertified 612
    unfold RowCertified
    rw [show rowPrefix 612 = UpperProfileCertificateData.prefix612 by rfl]
    exact UpperProfileCertificateData.row612_certificate
  · change RowCertified 613
    unfold RowCertified
    rw [show rowPrefix 613 = UpperProfileCertificateData.prefix613 by rfl]
    exact UpperProfileCertificateData.row613_certificate
  · change RowCertified 614
    unfold RowCertified
    rw [show rowPrefix 614 = UpperProfileCertificateData.prefix614 by rfl]
    exact UpperProfileCertificateData.row614_certificate
  · change RowCertified 615
    unfold RowCertified
    rw [show rowPrefix 615 = UpperProfileCertificateData.prefix615 by rfl]
    exact UpperProfileCertificateData.row615_certificate
  · change RowCertified 616
    unfold RowCertified
    rw [show rowPrefix 616 = UpperProfileCertificateData.prefix616 by rfl]
    exact UpperProfileCertificateData.row616_certificate
  · change RowCertified 617
    unfold RowCertified
    rw [show rowPrefix 617 = UpperProfileCertificateData.prefix617 by rfl]
    exact UpperProfileCertificateData.row617_certificate
  · change RowCertified 618
    unfold RowCertified
    rw [show rowPrefix 618 = UpperProfileCertificateData.prefix618 by rfl]
    exact UpperProfileCertificateData.row618_certificate
  · change RowCertified 619
    unfold RowCertified
    rw [show rowPrefix 619 = UpperProfileCertificateData.prefix619 by rfl]
    exact UpperProfileCertificateData.row619_certificate
  · change RowCertified 620
    unfold RowCertified
    rw [show rowPrefix 620 = UpperProfileCertificateData.prefix620 by rfl]
    exact UpperProfileCertificateData.row620_certificate
  · change RowCertified 621
    unfold RowCertified
    rw [show rowPrefix 621 = UpperProfileCertificateData.prefix621 by rfl]
    exact UpperProfileCertificateData.row621_certificate
  · change RowCertified 622
    unfold RowCertified
    rw [show rowPrefix 622 = UpperProfileCertificateData.prefix622 by rfl]
    exact UpperProfileCertificateData.row622_certificate
  · change RowCertified 623
    unfold RowCertified
    rw [show rowPrefix 623 = UpperProfileCertificateData.prefix623 by rfl]
    exact UpperProfileCertificateData.row623_certificate
  · change RowCertified 624
    unfold RowCertified
    rw [show rowPrefix 624 = UpperProfileCertificateData.prefix624 by rfl]
    exact UpperProfileCertificateData.row624_certificate
  · change RowCertified 625
    unfold RowCertified
    rw [show rowPrefix 625 = UpperProfileCertificateData.prefix625 by rfl]
    exact UpperProfileCertificateData.row625_certificate
  · change RowCertified 626
    unfold RowCertified
    rw [show rowPrefix 626 = UpperProfileCertificateData.prefix626 by rfl]
    exact UpperProfileCertificateData.row626_certificate
  · change RowCertified 627
    unfold RowCertified
    rw [show rowPrefix 627 = UpperProfileCertificateData.prefix627 by rfl]
    exact UpperProfileCertificateData.row627_certificate
  · change RowCertified 628
    unfold RowCertified
    rw [show rowPrefix 628 = UpperProfileCertificateData.prefix628 by rfl]
    exact UpperProfileCertificateData.row628_certificate
  · change RowCertified 629
    unfold RowCertified
    rw [show rowPrefix 629 = UpperProfileCertificateData.prefix629 by rfl]
    exact UpperProfileCertificateData.row629_certificate
  · change RowCertified 630
    unfold RowCertified
    rw [show rowPrefix 630 = UpperProfileCertificateData.prefix630 by rfl]
    exact UpperProfileCertificateData.row630_certificate
  · change RowCertified 631
    unfold RowCertified
    rw [show rowPrefix 631 = UpperProfileCertificateData.prefix631 by rfl]
    exact UpperProfileCertificateData.row631_certificate
  · change RowCertified 632
    unfold RowCertified
    rw [show rowPrefix 632 = UpperProfileCertificateData.prefix632 by rfl]
    exact UpperProfileCertificateData.row632_certificate
  · change RowCertified 633
    unfold RowCertified
    rw [show rowPrefix 633 = UpperProfileCertificateData.prefix633 by rfl]
    exact UpperProfileCertificateData.row633_certificate
  · change RowCertified 634
    unfold RowCertified
    rw [show rowPrefix 634 = UpperProfileCertificateData.prefix634 by rfl]
    exact UpperProfileCertificateData.row634_certificate
  · change RowCertified 635
    unfold RowCertified
    rw [show rowPrefix 635 = UpperProfileCertificateData.prefix635 by rfl]
    exact UpperProfileCertificateData.row635_certificate
  · change RowCertified 636
    unfold RowCertified
    rw [show rowPrefix 636 = UpperProfileCertificateData.prefix636 by rfl]
    exact UpperProfileCertificateData.row636_certificate
  · change RowCertified 637
    unfold RowCertified
    rw [show rowPrefix 637 = UpperProfileCertificateData.prefix637 by rfl]
    exact UpperProfileCertificateData.row637_certificate
  · change RowCertified 638
    unfold RowCertified
    rw [show rowPrefix 638 = UpperProfileCertificateData.prefix638 by rfl]
    exact UpperProfileCertificateData.row638_certificate
  · change RowCertified 639
    unfold RowCertified
    rw [show rowPrefix 639 = UpperProfileCertificateData.prefix639 by rfl]
    exact UpperProfileCertificateData.row639_certificate
  · change RowCertified 640
    unfold RowCertified
    rw [show rowPrefix 640 = UpperProfileCertificateData.prefix640 by rfl]
    exact UpperProfileCertificateData.row640_certificate
  · change RowCertified 641
    unfold RowCertified
    rw [show rowPrefix 641 = UpperProfileCertificateData.prefix641 by rfl]
    exact UpperProfileCertificateData.row641_certificate
  · change RowCertified 642
    unfold RowCertified
    rw [show rowPrefix 642 = UpperProfileCertificateData.prefix642 by rfl]
    exact UpperProfileCertificateData.row642_certificate
  · change RowCertified 643
    unfold RowCertified
    rw [show rowPrefix 643 = UpperProfileCertificateData.prefix643 by rfl]
    exact UpperProfileCertificateData.row643_certificate
  · change RowCertified 644
    unfold RowCertified
    rw [show rowPrefix 644 = UpperProfileCertificateData.prefix644 by rfl]
    exact UpperProfileCertificateData.row644_certificate
  · change RowCertified 645
    unfold RowCertified
    rw [show rowPrefix 645 = UpperProfileCertificateData.prefix645 by rfl]
    exact UpperProfileCertificateData.row645_certificate
  · change RowCertified 646
    unfold RowCertified
    rw [show rowPrefix 646 = UpperProfileCertificateData.prefix646 by rfl]
    exact UpperProfileCertificateData.row646_certificate
  · change RowCertified 647
    unfold RowCertified
    rw [show rowPrefix 647 = UpperProfileCertificateData.prefix647 by rfl]
    exact UpperProfileCertificateData.row647_certificate
  · change RowCertified 648
    unfold RowCertified
    rw [show rowPrefix 648 = UpperProfileCertificateData.prefix648 by rfl]
    exact UpperProfileCertificateData.row648_certificate
  · change RowCertified 649
    unfold RowCertified
    rw [show rowPrefix 649 = UpperProfileCertificateData.prefix649 by rfl]
    exact UpperProfileCertificateData.row649_certificate
  · change RowCertified 650
    unfold RowCertified
    rw [show rowPrefix 650 = UpperProfileCertificateData.prefix650 by rfl]
    exact UpperProfileCertificateData.row650_certificate
  · change RowCertified 651
    unfold RowCertified
    rw [show rowPrefix 651 = UpperProfileCertificateData.prefix651 by rfl]
    exact UpperProfileCertificateData.row651_certificate
  · change RowCertified 652
    unfold RowCertified
    rw [show rowPrefix 652 = UpperProfileCertificateData.prefix652 by rfl]
    exact UpperProfileCertificateData.row652_certificate
  · change RowCertified 653
    unfold RowCertified
    rw [show rowPrefix 653 = UpperProfileCertificateData.prefix653 by rfl]
    exact UpperProfileCertificateData.row653_certificate
  · change RowCertified 654
    unfold RowCertified
    rw [show rowPrefix 654 = UpperProfileCertificateData.prefix654 by rfl]
    exact UpperProfileCertificateData.row654_certificate
  · change RowCertified 655
    unfold RowCertified
    rw [show rowPrefix 655 = UpperProfileCertificateData.prefix655 by rfl]
    exact UpperProfileCertificateData.row655_certificate
  · change RowCertified 656
    unfold RowCertified
    rw [show rowPrefix 656 = UpperProfileCertificateData.prefix656 by rfl]
    exact UpperProfileCertificateData.row656_certificate
  · change RowCertified 657
    unfold RowCertified
    rw [show rowPrefix 657 = UpperProfileCertificateData.prefix657 by rfl]
    exact UpperProfileCertificateData.row657_certificate
  · change RowCertified 658
    unfold RowCertified
    rw [show rowPrefix 658 = UpperProfileCertificateData.prefix658 by rfl]
    exact UpperProfileCertificateData.row658_certificate
  · change RowCertified 659
    unfold RowCertified
    rw [show rowPrefix 659 = UpperProfileCertificateData.prefix659 by rfl]
    exact UpperProfileCertificateData.row659_certificate
  · change RowCertified 660
    unfold RowCertified
    rw [show rowPrefix 660 = UpperProfileCertificateData.prefix660 by rfl]
    exact UpperProfileCertificateData.row660_certificate
  · change RowCertified 661
    unfold RowCertified
    rw [show rowPrefix 661 = UpperProfileCertificateData.prefix661 by rfl]
    exact UpperProfileCertificateData.row661_certificate
  · change RowCertified 662
    unfold RowCertified
    rw [show rowPrefix 662 = UpperProfileCertificateData.prefix662 by rfl]
    exact UpperProfileCertificateData.row662_certificate
  · change RowCertified 663
    unfold RowCertified
    rw [show rowPrefix 663 = UpperProfileCertificateData.prefix663 by rfl]
    exact UpperProfileCertificateData.row663_certificate
  · change RowCertified 664
    unfold RowCertified
    rw [show rowPrefix 664 = UpperProfileCertificateData.prefix664 by rfl]
    exact UpperProfileCertificateData.row664_certificate
  · change RowCertified 665
    unfold RowCertified
    rw [show rowPrefix 665 = UpperProfileCertificateData.prefix665 by rfl]
    exact UpperProfileCertificateData.row665_certificate
  · change RowCertified 666
    unfold RowCertified
    rw [show rowPrefix 666 = UpperProfileCertificateData.prefix666 by rfl]
    exact UpperProfileCertificateData.row666_certificate
  · change RowCertified 667
    unfold RowCertified
    rw [show rowPrefix 667 = UpperProfileCertificateData.prefix667 by rfl]
    exact UpperProfileCertificateData.row667_certificate
  · change RowCertified 668
    unfold RowCertified
    rw [show rowPrefix 668 = UpperProfileCertificateData.prefix668 by rfl]
    exact UpperProfileCertificateData.row668_certificate
  · change RowCertified 669
    unfold RowCertified
    rw [show rowPrefix 669 = UpperProfileCertificateData.prefix669 by rfl]
    exact UpperProfileCertificateData.row669_certificate
  · change RowCertified 670
    unfold RowCertified
    rw [show rowPrefix 670 = UpperProfileCertificateData.prefix670 by rfl]
    exact UpperProfileCertificateData.row670_certificate
  · change RowCertified 671
    unfold RowCertified
    rw [show rowPrefix 671 = UpperProfileCertificateData.prefix671 by rfl]
    exact UpperProfileCertificateData.row671_certificate
  · change RowCertified 672
    unfold RowCertified
    rw [show rowPrefix 672 = UpperProfileCertificateData.prefix672 by rfl]
    exact UpperProfileCertificateData.row672_certificate
  · change RowCertified 673
    unfold RowCertified
    rw [show rowPrefix 673 = UpperProfileCertificateData.prefix673 by rfl]
    exact UpperProfileCertificateData.row673_certificate
  · change RowCertified 674
    unfold RowCertified
    rw [show rowPrefix 674 = UpperProfileCertificateData.prefix674 by rfl]
    exact UpperProfileCertificateData.row674_certificate
  · change RowCertified 675
    unfold RowCertified
    rw [show rowPrefix 675 = UpperProfileCertificateData.prefix675 by rfl]
    exact UpperProfileCertificateData.row675_certificate
  · change RowCertified 676
    unfold RowCertified
    rw [show rowPrefix 676 = UpperProfileCertificateData.prefix676 by rfl]
    exact UpperProfileCertificateData.row676_certificate
  · change RowCertified 677
    unfold RowCertified
    rw [show rowPrefix 677 = UpperProfileCertificateData.prefix677 by rfl]
    exact UpperProfileCertificateData.row677_certificate
  · change RowCertified 678
    unfold RowCertified
    rw [show rowPrefix 678 = UpperProfileCertificateData.prefix678 by rfl]
    exact UpperProfileCertificateData.row678_certificate
  · change RowCertified 679
    unfold RowCertified
    rw [show rowPrefix 679 = UpperProfileCertificateData.prefix679 by rfl]
    exact UpperProfileCertificateData.row679_certificate
  · change RowCertified 680
    unfold RowCertified
    rw [show rowPrefix 680 = UpperProfileCertificateData.prefix680 by rfl]
    exact UpperProfileCertificateData.row680_certificate
  · change RowCertified 681
    unfold RowCertified
    rw [show rowPrefix 681 = UpperProfileCertificateData.prefix681 by rfl]
    exact UpperProfileCertificateData.row681_certificate
  · change RowCertified 682
    unfold RowCertified
    rw [show rowPrefix 682 = UpperProfileCertificateData.prefix682 by rfl]
    exact UpperProfileCertificateData.row682_certificate
  · change RowCertified 683
    unfold RowCertified
    rw [show rowPrefix 683 = UpperProfileCertificateData.prefix683 by rfl]
    exact UpperProfileCertificateData.row683_certificate
  · change RowCertified 684
    unfold RowCertified
    rw [show rowPrefix 684 = UpperProfileCertificateData.prefix684 by rfl]
    exact UpperProfileCertificateData.row684_certificate
  · change RowCertified 685
    unfold RowCertified
    rw [show rowPrefix 685 = UpperProfileCertificateData.prefix685 by rfl]
    exact UpperProfileCertificateData.row685_certificate
  · change RowCertified 686
    unfold RowCertified
    rw [show rowPrefix 686 = UpperProfileCertificateData.prefix686 by rfl]
    exact UpperProfileCertificateData.row686_certificate
  · change RowCertified 687
    unfold RowCertified
    rw [show rowPrefix 687 = UpperProfileCertificateData.prefix687 by rfl]
    exact UpperProfileCertificateData.row687_certificate
  · change RowCertified 688
    unfold RowCertified
    rw [show rowPrefix 688 = UpperProfileCertificateData.prefix688 by rfl]
    exact UpperProfileCertificateData.row688_certificate
  · change RowCertified 689
    unfold RowCertified
    rw [show rowPrefix 689 = UpperProfileCertificateData.prefix689 by rfl]
    exact UpperProfileCertificateData.row689_certificate
  · change RowCertified 690
    unfold RowCertified
    rw [show rowPrefix 690 = UpperProfileCertificateData.prefix690 by rfl]
    exact UpperProfileCertificateData.row690_certificate
  · change RowCertified 691
    unfold RowCertified
    rw [show rowPrefix 691 = UpperProfileCertificateData.prefix691 by rfl]
    exact UpperProfileCertificateData.row691_certificate
  · change RowCertified 692
    unfold RowCertified
    rw [show rowPrefix 692 = UpperProfileCertificateData.prefix692 by rfl]
    exact UpperProfileCertificateData.row692_certificate
  · change RowCertified 693
    unfold RowCertified
    rw [show rowPrefix 693 = UpperProfileCertificateData.prefix693 by rfl]
    exact UpperProfileCertificateData.row693_certificate
  · change RowCertified 694
    unfold RowCertified
    rw [show rowPrefix 694 = UpperProfileCertificateData.prefix694 by rfl]
    exact UpperProfileCertificateData.row694_certificate
  · change RowCertified 695
    unfold RowCertified
    rw [show rowPrefix 695 = UpperProfileCertificateData.prefix695 by rfl]
    exact UpperProfileCertificateData.row695_certificate
  · change RowCertified 696
    unfold RowCertified
    rw [show rowPrefix 696 = UpperProfileCertificateData.prefix696 by rfl]
    exact UpperProfileCertificateData.row696_certificate
  · change RowCertified 697
    unfold RowCertified
    rw [show rowPrefix 697 = UpperProfileCertificateData.prefix697 by rfl]
    exact UpperProfileCertificateData.row697_certificate
  · change RowCertified 698
    unfold RowCertified
    rw [show rowPrefix 698 = UpperProfileCertificateData.prefix698 by rfl]
    exact UpperProfileCertificateData.row698_certificate
  · change RowCertified 699
    unfold RowCertified
    rw [show rowPrefix 699 = UpperProfileCertificateData.prefix699 by rfl]
    exact UpperProfileCertificateData.row699_certificate
  · change RowCertified 700
    unfold RowCertified
    rw [show rowPrefix 700 = UpperProfileCertificateData.prefix700 by rfl]
    exact UpperProfileCertificateData.row700_certificate
  · change RowCertified 701
    unfold RowCertified
    rw [show rowPrefix 701 = UpperProfileCertificateData.prefix701 by rfl]
    exact UpperProfileCertificateData.row701_certificate
  · change RowCertified 702
    unfold RowCertified
    rw [show rowPrefix 702 = UpperProfileCertificateData.prefix702 by rfl]
    exact UpperProfileCertificateData.row702_certificate
  · change RowCertified 703
    unfold RowCertified
    rw [show rowPrefix 703 = UpperProfileCertificateData.prefix703 by rfl]
    exact UpperProfileCertificateData.row703_certificate
  · change RowCertified 704
    unfold RowCertified
    rw [show rowPrefix 704 = UpperProfileCertificateData.prefix704 by rfl]
    exact UpperProfileCertificateData.row704_certificate
  · change RowCertified 705
    unfold RowCertified
    rw [show rowPrefix 705 = UpperProfileCertificateData.prefix705 by rfl]
    exact UpperProfileCertificateData.row705_certificate
  · change RowCertified 706
    unfold RowCertified
    rw [show rowPrefix 706 = UpperProfileCertificateData.prefix706 by rfl]
    exact UpperProfileCertificateData.row706_certificate
  · change RowCertified 707
    unfold RowCertified
    rw [show rowPrefix 707 = UpperProfileCertificateData.prefix707 by rfl]
    exact UpperProfileCertificateData.row707_certificate
  · change RowCertified 708
    unfold RowCertified
    rw [show rowPrefix 708 = UpperProfileCertificateData.prefix708 by rfl]
    exact UpperProfileCertificateData.row708_certificate
  · change RowCertified 709
    unfold RowCertified
    rw [show rowPrefix 709 = UpperProfileCertificateData.prefix709 by rfl]
    exact UpperProfileCertificateData.row709_certificate
  · change RowCertified 710
    unfold RowCertified
    rw [show rowPrefix 710 = UpperProfileCertificateData.prefix710 by rfl]
    exact UpperProfileCertificateData.row710_certificate
  · change RowCertified 711
    unfold RowCertified
    rw [show rowPrefix 711 = UpperProfileCertificateData.prefix711 by rfl]
    exact UpperProfileCertificateData.row711_certificate
  · change RowCertified 712
    unfold RowCertified
    rw [show rowPrefix 712 = UpperProfileCertificateData.prefix712 by rfl]
    exact UpperProfileCertificateData.row712_certificate
  · change RowCertified 713
    unfold RowCertified
    rw [show rowPrefix 713 = UpperProfileCertificateData.prefix713 by rfl]
    exact UpperProfileCertificateData.row713_certificate
  · change RowCertified 714
    unfold RowCertified
    rw [show rowPrefix 714 = UpperProfileCertificateData.prefix714 by rfl]
    exact UpperProfileCertificateData.row714_certificate
  · change RowCertified 715
    unfold RowCertified
    rw [show rowPrefix 715 = UpperProfileCertificateData.prefix715 by rfl]
    exact UpperProfileCertificateData.row715_certificate
  · change RowCertified 716
    unfold RowCertified
    rw [show rowPrefix 716 = UpperProfileCertificateData.prefix716 by rfl]
    exact UpperProfileCertificateData.row716_certificate
  · change RowCertified 717
    unfold RowCertified
    rw [show rowPrefix 717 = UpperProfileCertificateData.prefix717 by rfl]
    exact UpperProfileCertificateData.row717_certificate
  · change RowCertified 718
    unfold RowCertified
    rw [show rowPrefix 718 = UpperProfileCertificateData.prefix718 by rfl]
    exact UpperProfileCertificateData.row718_certificate
  · change RowCertified 719
    unfold RowCertified
    rw [show rowPrefix 719 = UpperProfileCertificateData.prefix719 by rfl]
    exact UpperProfileCertificateData.row719_certificate
run_cmd Lean.logInfo "FINER REAL INTERFACE: completed rows 600 through 719"
theorem all_certificates (i : Fin 720) : RowCertified i.val := by
  have hi := i.isLt
  by_cases h0 : i.val < 120
  · exact rows0 ⟨i.val,h0⟩
  by_cases h1 : i.val < 240
  · have hk : i.val-120<120 := by omega
    have he : i.val-120+120=i.val := by omega
    simpa only [he] using rows1 ⟨i.val-120,hk⟩
  by_cases h2 : i.val < 360
  · have hk : i.val-240<120 := by omega
    have he : i.val-240+240=i.val := by omega
    simpa only [he] using rows2 ⟨i.val-240,hk⟩
  by_cases h3 : i.val < 480
  · have hk : i.val-360<120 := by omega
    have he : i.val-360+360=i.val := by omega
    simpa only [he] using rows3 ⟨i.val-360,hk⟩
  by_cases h4 : i.val < 600
  · have hk : i.val-480<120 := by omega
    have he : i.val-480+480=i.val := by omega
    simpa only [he] using rows4 ⟨i.val-480,hk⟩
  have hk : i.val-600<120 := by omega
  have he : i.val-600+600=i.val := by omega
  simpa only [he] using rows5 ⟨i.val-600,hk⟩

theorem value_nonneg (j : ℕ) : 0 ≤ value j := by unfold value; positivity

theorem coefficient_nonneg (j : Fin 720) : 0 ≤ coefficient j.val := by
  unfold coefficient value
  apply sub_nonneg.mpr
  exact div_le_div_of_nonneg_right (by exact_mod_cast UpperProfileCertificateData.height_decreases j)
    (by norm_num [scale])

theorem value_terminal : value 720=0 := by
  simp only [value, UpperProfileCertificateData.height_terminal, Nat.cast_zero, zero_div]

theorem numeric_row (i : Fin 720) :
    (forceEntry i.val (rowPrefix i.val) : ℝ)/scale+1/10000+1/100000+
      (∑ j ∈ Finset.range 720, ((matrixEntry i.val (rowPrefix i.val) j : ℝ)/scale)*coefficient j)
      ≤ value i.val := by
  have hs : (((∑ j ∈ Finset.range 720, matrixEntry i.val (rowPrefix i.val) j*
      (UpperProfileCertificateData.height j-UpperProfileCertificateData.height (j+1))) : ℕ) : ℝ) =
      ∑ j ∈ Finset.range 720, (matrixEntry i.val (rowPrefix i.val) j : ℝ)*
        ((UpperProfileCertificateData.height j : ℝ)-(UpperProfileCertificateData.height (j+1) : ℝ)) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.cast_mul, Nat.cast_sub (UpperProfileCertificateData.height_decreases ⟨j, Finset.mem_range.mp hj⟩)]
  have h := (show (((scale*forceEntry i.val (rowPrefix i.val)+scale*(scale/10000)+scale*(scale/100000)+
    (∑ j ∈ Finset.range 720, matrixEntry i.val (rowPrefix i.val) j*
      (UpperProfileCertificateData.height j-UpperProfileCertificateData.height (j+1)))) : ℕ) : ℝ)
    ≤ ((scale*UpperProfileCertificateData.height i.val : ℕ) : ℝ) by
      exact_mod_cast (all_certificates i).2.2)
  push_cast only [Nat.cast_add, Nat.cast_mul] at h
  rw [hs] at h
  norm_num only [scale, Nat.reduceDiv, Nat.cast_ofNat] at h
  have hd := div_le_div_of_nonneg_right h (show (0 : ℝ)≤1000000000000000000000000 by norm_num)
  convert hd using 1
  · simp only [coefficient, value, scale, Nat.cast_ofNat]
    rw [add_div, add_div, add_div, Finset.sum_div]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  · simp only [value, scale, Nat.cast_ofNat]
    ring

theorem rowBudget (i : Fin 720) :
    forcingRectangles i.val+
      (∑ j ∈ Finset.range 720, cumulativeRectangles i.val j*coefficient j)+
      1/10000+1/100000 ≤ value i.val := by
  have hc := (all_certificates i).1
  have hz := (all_certificates i).2.1
  have hf := forcing_prefix_bound i.val (rowPrefix i.val) hc hz
  have hs : (∑ j ∈ Finset.range 720, cumulativeRectangles i.val j*coefficient j) ≤
      (∑ j ∈ Finset.range 720, ((matrixEntry i.val (rowPrefix i.val) j : ℝ)/scale)*coefficient j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right
      (cumulative_prefix_bound i.val j (rowPrefix i.val) (Finset.mem_range.mp hj) hc hz)
      (coefficient_nonneg ⟨j, Finset.mem_range.mp hj⟩)
  have hb := numeric_row i
  linarith

theorem finite_area_exact :
    (∑ j ∈ Finset.range 720, coefficient j*(cut j-2)) =
      (3068866243439/5000000000000 : ℝ) := by
  change (∑ j ∈ Finset.range 720, (value j-value (j+1))*(cut j-2)) = _
  rw [area_identity value 720 value_terminal]
  simp only [value, ← Finset.sum_div, ← Nat.cast_sum]
  rw [UpperProfileCertificateData.height_sum]
  norm_num [scale]

theorem finite_area_lt :
    (∑ j ∈ Finset.range 720, coefficient j*(cut j-2)) < (307/500 : ℝ) := by
  rw [finite_area_exact]
  norm_num

run_cmd do
  for decl in [``all_certificates, ``value_nonneg, ``coefficient_nonneg, ``value_terminal,
      ``numeric_row, ``rowBudget, ``finite_area_exact, ``finite_area_lt] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "720 ROW POSTFIXED REAL PROFILE AND EXACT AREA CERTIFICATE"
end UpperProfileCertificate
end
