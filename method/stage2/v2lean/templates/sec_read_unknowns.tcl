# Sequential SEC with a free-running clock environment (Jasper clock -none).
# No periodic-clock, reset-sequence or reset-inactive assumption is imposed.
# State mappings are relational correspondence obligations of the SEC flow.
# Flow reference: hkust-zhiyao/DR_RTL, syn_flow_eda/scr/sec.tcl.
# Result/query commands checked against Jasper 24.06 help on usr.
source config.tcl
set status_file [open run_status.txt w]
if {[catch {
    clear -all
    check_sec -analyze -spec -sv original.v
    check_sec -analyze -imp -sv roundtrip.v
    check_sec -elaborate -spec -top $v2lean_top -disable_auto_bbox
    check_sec -elaborate -imp -top $v2lean_top -disable_auto_bbox
    check_sec -setup -no_auto_mapping
    check_sec -auto_map_reset_x_values off
    check_sec -map -auto
    foreach pair $v2lean_initial_pairs {
        lassign $pair spec_q imp_q
        # -init relates arbitrary initial Q values for ONE initial bound only.
        # It adds no invariant assumption about subsequent output/state equality.
        check_sec -map -spec $spec_q -imp $imp_q -init
    }
    # The certificate proposes only free out-of-bounds read values. Require
    # exact independently elaborated signal sets, including width and origins.
    set spec_reads [check_sec -list -signal -spec -signal_type x_index_out_of_range]
    set imp_reads [check_sec -list -signal -imp -signal_type x_index_out_of_range]
    set expected_spec {}
    set expected_imp {}
    foreach pair $v2lean_read_pairs {
        lassign $pair spec_read imp_read
        lappend expected_spec $spec_read
        lappend expected_imp $imp_read
    }
    if {[lsort $spec_reads] ne [lsort $expected_spec] || [lsort $imp_reads] ne [lsort $expected_imp]} {
        error "Read-X certificate differs from elaborated out-of-bounds signals"
    }
    foreach side {spec imp} expected [list $expected_spec $expected_imp] {
        foreach kind {x_bus_contention x_assignment} {
            if {[llength [check_sec -list -signal -$side -signal_type $kind]] != 0} {
                error "Read-X certificate cannot cover $side $kind"
            }
        }
        if {[lsort [check_sec -list -signal -$side -signal_type undriven]] ne [lsort $expected]} {
            error "Read-X certificate cannot cover other $side undriven signals"
        }
    }
    set read_signals [open read_signals.tsv w]
    foreach pair $v2lean_read_pairs {
        lassign $pair spec_read imp_read
        puts $read_signals "$spec_read\t$imp_read"
        check_sec -map -spec $spec_read -imp $imp_read
    }
    close $read_signals
    clock -none
    reset -none
    check_sec -interface
    check_sec -gen
    check_sec -prove -strategy proof
    check_assumptions -task <embedded> -conflict
    check_sec -signoff -file signoff.json -json
    check_sec -signoff -file signoff.txt
    set mapping_data [check_sec -list -mapping -task <embedded> -include_global_mapping -return dict]
    if {[llength $mapping_data] == 0} { error "SEC mapping evidence is empty" }
    set mappings [open mapping.txt w]
    puts $mappings $mapping_data
    close $mappings
    set properties [open properties.tsv w]
    foreach output $v2lean_outputs {
        set property "<embedded>::$output"
        puts $properties "$output\t[get_property_info -list status $property]"
    }
    close $properties
    puts $status_file COMPLETE
} error options]} {
    puts $status_file ERROR
    puts $status_file $error
    puts $status_file [dict get $options -errorinfo]
    puts stderr [dict get $options -errorinfo]
}
close $status_file
exit
