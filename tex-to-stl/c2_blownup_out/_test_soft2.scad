explode=1.04; hull_scale=0.98; G=[-0.04126,0.10202,-0.35364];
round_r=0.08;   // fillet radius on cell shoulders
shrink=0.93;    // pre-shrink each cell about its centroid to keep gaps open
sfn=12;
function ec(c)=c+(explode-1)*(c-G);           // exploded cell centroid
module cell(f,c){ translate((explode-1)*(c-G)) import(f); }
module cellh(f,c){ hull() cell(f,c); }
// rounded, gap-preserving cell
module cellr(f,c){
  minkowski(){
    translate(ec(c)) scale(shrink) translate(-ec(c)) cell(f,c);
    sphere(r=round_r,$fn=sfn);
  }
}
module cellsr(){
 cellr("../c2_congruent_out/shell_321-0.stl",[0.16023,3.47832,-0.88348]);
 cellr("../c2_congruent_out/shell_421-1.stl",[1.55644,2.63588,0.51583]);
 cellr("../c2_congruent_out/shell_431-11.stl",[-3.36003,1.92420,-0.98675]);
 cellr("../c2_congruent_out/shell_432-111.stl",[2.21157,1.56129,-3.61003]);
 cellr("../c2_congruent_out/shell_521-3.stl",[1.28339,0.94733,2.47436]);
 cellr("../c2_congruent_out/shell_531-21.stl",[-1.45965,0.38968,1.68466]);
 cellr("../c2_congruent_out/shell_532-211.stl",[3.57420,0.70670,-2.21238]);
 cellr("../c2_congruent_out/shell_541-33.stl",[-4.59616,-0.39244,-2.77138]);
 cellr("../c2_congruent_out/shell_542-221.stl",[-2.22879,-0.52123,-3.86091]);
 cellr("../c2_congruent_out/shell_621-5.stl",[1.70161,-0.88950,2.81972]);
 cellr("../c2_congruent_out/shell_631-51.stl",[-0.64697,-1.93286,2.74440]);
 cellr("../c2_congruent_out/shell_632-411.stl",[3.44571,-1.51895,-0.12201]);
 cellr("../c2_congruent_out/shell_641-43.stl",[-2.30101,-2.57042,0.25861]);
 cellr("../c2_congruent_out/shell_642-321.stl",[0.08181,-2.38971,-1.00163]);
}
module cellsh(){
 cellh("../c2_congruent_out/shell_321-0.stl",[0.16023,3.47832,-0.88348]);
 cellh("../c2_congruent_out/shell_421-1.stl",[1.55644,2.63588,0.51583]);
 cellh("../c2_congruent_out/shell_431-11.stl",[-3.36003,1.92420,-0.98675]);
 cellh("../c2_congruent_out/shell_432-111.stl",[2.21157,1.56129,-3.61003]);
 cellh("../c2_congruent_out/shell_521-3.stl",[1.28339,0.94733,2.47436]);
 cellh("../c2_congruent_out/shell_531-21.stl",[-1.45965,0.38968,1.68466]);
 cellh("../c2_congruent_out/shell_532-211.stl",[3.57420,0.70670,-2.21238]);
 cellh("../c2_congruent_out/shell_541-33.stl",[-4.59616,-0.39244,-2.77138]);
 cellh("../c2_congruent_out/shell_542-221.stl",[-2.22879,-0.52123,-3.86091]);
 cellh("../c2_congruent_out/shell_621-5.stl",[1.70161,-0.88950,2.81972]);
 cellh("../c2_congruent_out/shell_631-51.stl",[-0.64697,-1.93286,2.74440]);
 cellh("../c2_congruent_out/shell_632-411.stl",[3.44571,-1.51895,-0.12201]);
 cellh("../c2_congruent_out/shell_641-43.stl",[-2.30101,-2.57042,0.25861]);
 cellh("../c2_congruent_out/shell_642-321.stl",[0.08181,-2.38971,-1.00163]);
}
union(){
  cellsr();
  translate(G) scale(hull_scale) translate(-G) hull() cellsh();
}
