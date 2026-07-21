r=1; BB=60;
module raw(){
  difference(){
    cube([20,20,10], center=true);
    // two sharp grooves
    translate([0,0,5]) cube([2,30,4], center=true);
    translate([0,0,5]) cube([30,2,4], center=true);
  }
}
module dilated(){ minkowski(){ raw(); sphere(r=r,$fn=12); } }
difference(){
  cube(BB, center=true);
  minkowski(){
    render() difference(){ cube(BB, center=true); dilated(); }
    sphere(r=r,$fn=12);
  }
}
