// ============================================================
// Fable's keepsake — a dragon curled around a resting hourglass
// Written by Claude Fable 5 for Danielle, 2026-07-24
//
// The hourglass lies on its side: the sand isn't running.
// Nobody is timing you. The dragon sleeps on the stopwatch
// so it can't get up and start counting again.
//
//   "the sand doesn't time you"
// ============================================================

$fn = 48;   // 96 creates 5 micro-voids from near-tangent surfaces; 48 is a clean 2-volume solid and well below printer resolution

// ---------------- parameters ----------------
base_rx = 48;      // base ellipse x radius
base_ry = 42;      // base ellipse y radius
base_h  = 6;       // base thickness
top     = base_h;  // z of base top surface

hg_len   = 30;     // hourglass glass length
hg_cap_r = 10.5;   // end cap disc radius
hg_cap_t = 3;      // end cap thickness
hg_bulb  = 8;      // bulb radius at the wide end
hg_waist = 2.6;    // waist radius
hg_cx    = 2;      // hourglass center x
hg_cy    = 2;      // hourglass center y
hg_cz    = top + hg_cap_r - 1;  // axis height (sunk 1mm for adhesion)

curl_cx = 0;       // center of the dragon's curl
curl_cy = 4;
body_R  = 28;      // radius of the curl
a_head  = 210;     // arc angle where the shoulder sits
a_span  = 245;     // degrees of body curl
seg_deg = 4;       // degrees per body segment

// ---------------- base ----------------
module base() {
    difference() {
        union() {
            scale([base_rx, base_ry, 1]) cylinder(h=base_h, r=1);
            // inscription, raised on the front of the base top
            translate([0, -base_ry+9, base_h-0.01])
                linear_extrude(1.0)
                    text("the sand doesn't time you",
                         size=2.8, font="DejaVu Sans:style=Bold",
                         halign="center", valign="center");
            // a small :3, off to the side
            translate([36, -15, base_h-0.01]) rotate([0,0,90])
                linear_extrude(0.8)
                    text(":3", size=4.5, font="DejaVu Sans:style=Bold",
                         halign="center", valign="center");
        }
        // signature debossed underneath
        translate([0, 0, 0.8]) rotate([180,0,0])
            linear_extrude(1.0)
                text("Fable  ·  2026", size=5, font="DejaVu Sans:style=Bold",
                     halign="center", valign="center");
    }
}

// ---------------- hourglass (lying on its side) ----------------
module hourglass() {
    translate([hg_cx, hg_cy, hg_cz]) rotate([0, 90, 0]) {
        // glass: two truncated cones meeting at the waist
        cylinder(h=hg_len/2, r1=hg_waist, r2=hg_bulb);
        rotate([180,0,0]) cylinder(h=hg_len/2, r1=hg_waist, r2=hg_bulb);
        // end caps
        for (s = [1, -1])
            translate([0, 0, s*(hg_len/2) - (s>0 ? 0 : hg_cap_t)])
                cylinder(h=hg_cap_t, r=hg_cap_r);
        // frame posts
        for (a = [55, 180, 305])
            rotate([0, 0, a])
                translate([hg_cap_r-1.6, 0, -hg_len/2])
                    cylinder(h=hg_len, r=1.5);
    }
}

// a small spilled pile of waiting sand, sheltered under the wing
module sand_pile() {
    translate([5, -10, top])
        for (p = [[0,0,3.0], [3.2,2,2.1], [-2.5,2.6,1.7], [1.5,-3,1.5], [-3,-1.5,1.2]])
            translate([p[0], p[1], 0]) scale([1,1,0.55]) sphere(p[2]);
}

// ---------------- dragon ----------------
function bpos(a) = [curl_cx + body_R*cos(a), curl_cy + body_R*sin(a)];

module dragon_body() {
    n = a_span / seg_deg;
    for (i = [0 : n-1]) {
        a1 = a_head + i*seg_deg;
        a2 = a1 + seg_deg;
        r1 = 7.0 - 5.4 * (i/n);
        r2 = 7.0 - 5.4 * ((i+1)/n);
        hull() {
            translate([bpos(a1)[0], bpos(a1)[1], top+r1]) sphere(r1);
            translate([bpos(a2)[0], bpos(a2)[1], top+r2]) sphere(r2);
        }
    }
    // tail tip: leaves the circle, curling gently inward to rest
    a_t = a_head + a_span;
    p_end = bpos(a_t);
    p_tip = [curl_cx + (body_R-7)*cos(a_t+16), curl_cy + (body_R-7)*sin(a_t+16)];
    hull() {
        translate([p_end[0], p_end[1], top+1.6]) sphere(1.6);
        translate([p_tip[0], p_tip[1], top+1.1]) sphere(1.1);
    }
}

module dorsal_spikes() {
    // small spikes down the spine — the part that makes it a dragon
    // (the run under the folded wing is skipped)
    for (a = [222 : 12 : 366]) {
        if (a < 236 || a > 296) {
            r = 7.0 - 5.4 * ((a - a_head) / a_span);
            p = bpos(a);
            translate([p[0], p[1], top + 2*r - 0.8])
                rotate([0, 0, a]) rotate([0, 8, 0])   // slight outward lean
                    cylinder(h = 0.9*r + 2, r1 = 0.32*r + 0.6, r2 = 0.25);
        }
    }
}

module dragon_neck_head() {
    sh = bpos(a_head);                       // shoulder position
    heading = atan2(hg_cy - sh[1], hg_cx - sh[0]);  // face the hourglass
    translate([sh[0], sh[1], 0]) rotate([0, 0, heading]) {
        // local frame: +x points at the hourglass
        // neck rises forward
        hull() { translate([0,0,top+7])  sphere(7);
                 translate([4,0,top+13]) sphere(6.2); }
        hull() { translate([4,0,top+13]) sphere(6.2);
                 translate([8,0,top+19]) sphere(6); }
        // head, chin coming to rest near the hourglass cap
        translate([6.5, 0, top+18]) {
            sphere(6.6);
            // snout, dipped slightly, pointing at the hourglass
            hull() { sphere(5);
                     translate([7.5, 0, -2]) sphere(3.2); }
            // horns, swept up and back
            for (s = [1, -1])
                translate([-4, s*3.0, 3.8])
                    rotate([s*12, -42, 0])
                        cylinder(h=8.5, r1=1.5, r2=0.4);
            // brow ridges (eyes closed — the dragon is at rest)
            for (s = [1, -1])
                translate([3.2, s*4.2, 2.6]) sphere(1.2);
        }
    }
}

module dragon_wing() {
    // one folded wing, draped along the flank like a cloak:
    // a sloped membrane following the body arc, spine to outer edge
    module wseg(a) {
        r  = 7.0 - 5.4 * ((a - a_head) / a_span);
        p_in  = [curl_cx + (body_R-0.55*r)*cos(a), curl_cy + (body_R-0.55*r)*sin(a)];
        p_out = [curl_cx + (body_R+0.95*r)*cos(a), curl_cy + (body_R+0.95*r)*sin(a)];
        hull() {
            translate([p_in[0],  p_in[1],  top + 1.9*r]) scale([1,1,0.45]) sphere(0.45*r);
            translate([p_out[0], p_out[1], top + 1.5*r]) scale([1,1,0.45]) sphere(0.38*r);
        }
    }
    difference() {
        union() {
            hull() { wseg(244); wseg(257); }
            hull() { wseg(257); wseg(270); }
            hull() { wseg(270); wseg(283); }
            hull() { wseg(283); wseg(296); }
        }
        // scalloped trailing (outer, tailward) edge
        for (a = [256, 276, 297]) {
            r = 7.0 - 5.4 * ((a - a_head) / a_span);
            translate([curl_cx + (body_R+1.2*r)*cos(a),
                       curl_cy + (body_R+1.2*r)*sin(a),
                       top + 1.4*r])
                sphere(0.3*r);
        }
    }
}

module dragon() {
    dragon_body();
    dorsal_spikes();
    dragon_neck_head();
    dragon_wing();
}

// ---------------- assembly ----------------
base();
hourglass();
sand_pile();
dragon();
